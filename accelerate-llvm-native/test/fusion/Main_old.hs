-- |
-- Module      : nofib-llvm-native
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native
import Data.Array.Accelerate.LLVM.Native.Operation
import Criterion.Main
import Control.Monad
import Prelude (Show(..), IO, )
import qualified Prelude as Prelude
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate.Unsafe

main :: IO ()
main = do
  Prelude.print $ runN @Interpreter complex $ fromList (Z:.100) $ Prelude.map (`Prelude.mod` 50) [1 :: Int ..]
  -- benchmarking:
  -- defaultMain $ 
  --   Prelude.map (benchOption . Prelude.Left) [minBound :: Objective .. maxBound] 
  --   Prelude.++ 
  --   Prelude.map (benchOption . Prelude.Right) [NoFusion, GreedyFusion]

  -- Prelude.print $ runNWithObj @Native ArrayReadsWrites $ quicksort $ use $ fromList (Z :. 5) [100::Int, 200, 3, 5, 4]
  where
    benchOption :: Prelude.Either Objective Benchmarking -> Benchmark
    benchOption obj = bgroup (show obj)
      [ 
      --   benchProgram "diagonal " diagonal  obj
      -- , benchProgram "diagonal'" diagonal' obj
        benchProgram "complex" complex obj
      -- , benchProgram "complex'" complex' obj
      , benchProgram "complexAdd" complexAdd obj
      -- , benchProgram "complexAdd'" complexAdd' obj
      , benchProgram "singleLoop" singleLoop obj
      , benchProgram "singleLoop'" singleLoop' obj
      , benchProgram "futharkbadaccelerategood" futharkbadaccelerategood obj
      , benchProgram "reverses" reverses obj
      ]
    benchProgram str pr (Prelude.Left obj) = env (return $ runNWithObj @Native obj pr) $ \p -> bgroup str
      [ benchsize (32*32*32) p ]
    benchProgram str pr (Prelude.Right obj) = env (return $ runNBench @Native obj pr) $ \p -> bgroup str
      [ benchsize (32*32*32) p ] 
    xs n = fromList (Z:.n) $ Prelude.map (`Prelude.mod` (n `div` 2)) [1 :: Int ..]
    benchsize n p = env (return $ xs n) $ \xs -> bench (show n) $ nf p xs
      -- we force the result by indexing into a result array and forcing that number. 
      -- some benchmarks return two arrays, so we simply index in the first one
      -- [ env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native complex    )) $ (\ ~(xs, p) -> bench "complex    " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native complex'   )) $ (\ ~(xs, p) -> bench "complex'   " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native complexAdd )) $ (\ ~(xs, p) -> bench "complexAdd " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native complexAdd')) $ (\ ~(xs, p) -> bench "complexAdd'" $ nf p xs)         
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native singleLoop )) $ (\ ~(xs, p) -> bench "singleLoop " $ nf p xs)         
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native singleLoop')) $ (\ ~(xs, p) -> bench "singleLoop'" $ nf p xs) 
      -- [ bench "diagonal   " $ nf (flip linearIndexArray 0 . Prelude.fst . p) xs) 
      -- , bench "diagonal'  " $ nf (flip linearIndexArray 0 . Prelude.fst . p) xs) 
      -- ]

----------------------------BENCHMARKS------------------------------
-- complex      from the ILP example
-- complexAdd   a variation on complex, where the results are zipWith-ed together
-- singleLoop   from the introduction
-- diagonal     two maps, fused diagonally
--------------------------------------------------------------------

complex :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
complex xs = 
  let as = A.map (* 2)             xs
      bs = A.map (+ 3)             xs
      cs = A.map (\a -> bs ! I1 a) as
      ds = A.map (\b -> as ! I1 b) bs
  in T2 cs ds

complex' :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
complex' xs = 
  let as = A.map (* 2)             $ xs
      bs = A.map (+ 3)             $ barrier xs
      cs = A.map (\a -> bs ! I1 a) $ barrier as
      ds = A.map (\b -> as ! I1 b) $ barrier bs
    in T2 cs ds


complexAdd :: Acc (Vector Int) -> Acc (Vector Int)
complexAdd xs = 
  let as = A.map (* 2)             xs
      bs = A.map (+ 3)             xs
      cs = A.map (\a -> bs ! I1 a) as
      ds = A.map (\b -> as ! I1 b) bs
    in A.zipWith (+) cs ds

complexAdd' :: Acc (Vector Int) -> Acc (Vector Int)
complexAdd' xs = 
  let as = A.map (* 2)             $ xs
      bs = A.map (+ 3)             $ barrier xs
      cs = A.map (\a -> bs ! I1 a) $ barrier as
      ds = A.map (\b -> as ! I1 b) $ barrier bs
    in A.zipWith (+) cs ds

singleLoop :: Acc (Vector Int) -> Acc (Vector Int)
singleLoop as =
  let bs = A.reverse  as
      cs = A.map (+1) as
      ds = A.map (*2) cs
  in  A.zipWith3 (\b c d -> b + c + d) bs cs ds

-- mimicking delayed arrays: One cluster computing @cs@, and one with the zipWith3 that has @bs@ and @ds@ vertically fused.
singleLoop' :: Acc (Vector Int) -> Acc (Vector Int)
singleLoop' as =
  let bs = A.reverse  $ barrier $ as
      cs = A.map (+1) $ barrier $ as
      ds = A.map (*2) $ barrier $ cs
  in  A.zipWith3 (\b c d -> b + c + d) bs cs ds

-- something that showcases the use of awhileFuse, but sadly we also need something like fold to be implemented to make this work
mapWhilePositive :: Acc (Vector Int) -> Acc (Vector Int)
mapWhilePositive = awhileFuse (fold1 (A.&&) . A.map (A.> 0)) (A.map (\x -> x-1))

diagonal :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
diagonal xs = let ys = A.map (+2) xs in T2 ys (A.map (+3) ys)

diagonal' :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
diagonal' xs = let ys = A.map (+2) xs in T2 ys (A.map (+3) $ barrier ys)

futharkbadaccelerategood :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
futharkbadaccelerategood = complex . map (\x -> x - 1)




barrier :: Elt a => Acc (Vector a) -> Acc (Vector a)
barrier xs = generate (shape xs) (xs A.!)


vertical :: Acc (Vector Int) -> Acc (Vector Int)
vertical xs = let ys = A.map (+2) xs in A.map (+3) ys

--------------------------------------------------------

-- the map correctly doesn't get fused into the zip and reverse kernel
zippies :: Acc (Vector Int) -> Acc (Vector Int)
zippies (A.map (*2) -> xs) = A.zipWith6 (\a b c d e f -> a + b + c + d + e + f)
  xs
  xs
  xs
  xs
  (A.reverse xs)
  xs

reverses :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
reverses xs = let
  xs' = A.reverse xs
  a   = A.zip xs xs'
  b   = A.reverse a
  (c, d) = A.unzip b
  in T2 c (A.reverse d)


foo :: Acc (Vector Int) -> Acc (Vector Int)
foo = A.map (\(T2 a b) -> a + b) . A.map (\x -> T2 (x-1) (x+1))

-- A version of awhile that generates more code, as we duplicate the condition, but this allows it to fuse the condition into the body
awhileFuse :: Arrays a 
           => (Acc a -> Acc (Scalar Bool))    -- ^ keep evaluating while this returns 'True'
           -> (Acc a -> Acc a)                -- ^ function to apply
           -> Acc a                           -- ^ initial value
           -> Acc a
awhileFuse c f x = asnd $ A.awhile c' f' x'
  where
    x' = T2 (c x) x
    c' (T2 cond _) = cond
    f' (T2 _ value) = let value' = f value in T2 (c value') value'

------------------


-- new example to replace 'complex': needs to be easy, but have at least two local optima

-- example xs =
--   let as = map (+1) xs
--       bs = map (*2) xs
--   in permute (+) (\i -> i/2) as bs


