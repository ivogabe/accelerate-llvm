-- |
-- Module      : nofib-llvm-native
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
--
-- Portability : non-portable (GHC extensions)
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Main where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native
import Data.Array.Accelerate.LLVM.Native.Operation
import Criterion.Main
import Control.Monad
import Prelude (Show(..), IO, print, putStrLn)
import qualified Prelude as Prelude
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate.Unsafe
import Control.Concurrent
import Control.DeepSeq
-- import Quickhull
import Data.Array.Accelerate.Trafo.Partitioning.ILP (Benchmarking(..))
import Criterion.Types
import Data.Array.Accelerate (testWithObjective)

main :: IO ()
main = do

  let xs'= fromList (Z:.1000)       [1::Int ..]
      xs = fromList (Z:.10000000)       [1::Int ..]
      ys = fromList (Z:.1000:.1000) [1::Int ..]
      zs = fromList (Z:.1000:.1000) [0::Int ..]

  -- The forwards greedy algorithm can't (easily?) be fooled into manifesting a large array,
  -- but it does do this example 1.5-2x as slow
  let greedyForwardBad as = 
        let (I1 x) = shape as
            bs = map (*2) as
            cs = map (+1) bs
            xs = generate (Z_ ::. x) (\(I1 i) -> i + bs ! (I1 0))
            result = sum $ zipWith (+) cs xs
        in result
  -- backwards greedy manifests a huge array  
  let greedyBackwardBad (xs :: Acc (Vector Int)) =
        let large = replicate (Z_ ::. All_ ::. (1000000 :: Exp Int)) xs
            ys = sum large
            zs = product large
            result = imap (\(I1 i) y -> if zs ! (I1 0) == 0 then y else 1+y) ys
        in result

  let transpose' x =
        let sh ::. a ::. b = shape x
        in backpermute (sh ::. b ::. a) (\(sh ::. b ::. a) -> sh ::. a ::. b) x


  let matmul (T2 xs ys) = 
        let Z_ ::. rows ::. _    = shape xs
            Z_ ::. _    ::. cols = shape ys
        in sum $ transpose' $ zipWith (*)
            (replicate (Z_ ::. All_ ::. All_ ::. cols) xs)
            (replicate (Z_ ::. rows ::. All_ ::. All_) ys)
  
  let matmulcontext :: Acc (Matrix Int) -> Acc (Matrix Int)
      matmulcontext xs' =
        let xs = map (*2) xs'
            ys = map (+1) xs
            zs = map (`div` xs ! (Z_::.0::.0)) ys
        in matmul (T2 ys zs)

  let testcase' :: (Arrays a, Arrays b, NFData a, NFData b) => ((Acc a -> Acc b) -> a -> b) -> (Prelude.String, Acc a -> Acc b, a) -> Benchmark
      testcase' f (name, p, input) = env (Prelude.pure (f p, input)) $ \ ~(p', xs') -> bench name $ nf p' xs'

  let testcase :: Prelude.String -> (forall a b. (Arrays a, Arrays b) =>(Acc a -> Acc b) -> a -> b) -> Benchmark
      testcase name f = bgroup name 
        [ 
          -- testcase' f ("matmulcontext", matmulcontext, ys)
        --   testcase' f ("matmul", matmul, (ys, zs))
          testcase' f ("forwardbad",greedyForwardBad, xs)
        , testcase' f ("backwardbad", greedyBackwardBad, xs')
        ]
  
  -- benchmarkmain

  -- putStrLn "readswrites"
  -- putStrLn $ testWithObjective @UniformScheduleFun @NativeKernel IntermediateArrays (greedyForwardBad)
  -- putStrLn "down"
  -- putStrLn $ testBench   @UniformScheduleFun @NativeKernel GreedyDown (greedyForwardBad)
  -- putStrLn "up"
  -- putStrLn $ testBench   @UniformScheduleFun @NativeKernel GreedyUp (greedyForwardBad)
  
  

  defaultMainWith (defaultConfig { timeLimit = 5*60, resamples = 10000, csvFile = Just "greediesarebad.csv"}) $ Prelude.map (\obj -> testcase (show obj) (runNWithObj @Native obj))
    [ 
      Everything
    -- , NumClusters
    -- , ArrayReads
    --  ArrayReadsWrites
    -- , IntermediateArrays
    -- , FusedEdges
    ]
    Prelude.<> Prelude.map (\b -> testcase (show b) (runNBench @Native b))
    [ GreedyUp
    , GreedyDown
    , NoFusion
    ]



  -- let ys = map (\x -> x*x) $ 
  --           use xs
  -- let zs = sum $ reshape (Z_ ::. 5 ::. 10) ys
  -- let (zs, _) = A.unzip $ awhile (A.any (\(T2 a b) -> a <= 5) ) (map (\(T2 a b) -> T2 b (a+1))) ys

  -- let f = map (*2)
  -- let program = awhile (map (A.>0) . asnd) (\(T2 a b) -> T2 (f a) (map (\x -> x - 1) b)) (T2 ys $ unit $ constant (100000 :: Int))

  -- putStrLn "generate"
  -- let zs = generate (Z_ ::. 256 ::. 256) $ \idx -> if Prelude.foldl1 (||) $ Prelude.map (== idx) [I2 (constant a) (constant b) | a <- [205..209], b <- [200..210]] 
  --           then 1 
  --           else if Prelude.foldl1 (||) $ Prelude.map (== idx) [I2 (constant a) (constant b) | a <- [250..259], b <- [250..260]]
  --                   then -1
  --                   else 0 :: Exp Double


  -- let negatives = [
  --       I3 211 154 98,
  --       I3 102 138 112,
  --       I3 101 156 59,
  --       I3 17 205 32,
  --       I3 92 63 205,
  --       I3 199 7 203,
  --       I3 250 170 157,
  --       I3 82 184 255,
  --       I3 154 162 36,
  --       I3 223 42 240]
  --     positives = [
  --       I3 57 120 167,
  --       I3 5 118 175,
  --       I3 176 246 164,
  --       I3 45 194 234,
  --       I3 212 7 248,
  --       I3 115 123 207,
  --       I3 202 83 209,
  --       I3 203 18 198,
  --       I3 243 172 14,
  --       I3 54 209 40]

  -- let zs = generate (Z_ ::. constant 15 ::. constant 15 ::. constant 11) $ \(I3 x y z) -> T3 x y z
  --             -- cond (Prelude.foldl1 (||) $ Prelude.map (== idx) negatives)
  --             --   (-1)
  --             --   $ cond (Prelude.foldl1 (||) $ Prelude.map (==idx) positives)
  --             --     1
  --                 -- 0 :: Exp Double
  -- -- let zs' = zs $ use $ fromList Z [11 :: Int]
  -- putStrLn $ test @UniformScheduleFun @NativeKernel zs
  -- print $ run @Native zs

  -- putStrLn "scan:"
  -- let f = 
  --       --map (*2) $ 
  --       scanl1 (+) $
  --       --map (+4) $ 
  --       use xs
  -- putStrLn $ test @UniformScheduleFun @NativeKernel f
  -- print $ run @Native f

  -- putStrLn $ test @UniformScheduleFun @NativeKernel $ map (\(I2 a b)->b) (generate (I2 10 5) (\(I2 i j) -> fromIndex (I2 (5 :: Exp Int) (10 :: Exp Int)) (toIndex (I2 10 5) (I2 i j))))

  -- threadDelay 5000000
  -- putStrLn "done"
  -- threadDelay 5000000
  -- putStrLn "done"
  -- threadDelay 500000
  -- putStrLn "done"

  -- let program xs = 
  --   -- let xs = A.use (A.fromList (A.Z A.:. 10) ([0..] :: [Int])) in 
  --       A.map fst $ A.zip (A.reverse xs) (A.reverse $ A.backpermute (A.I1 10) Prelude.id (xs :: A.Acc (A.Vector Int)))
  -- -- let f = T2 (map (+1) ys) (map (*2) $ reverse ys)
  -- -- let f = sum $ map (\(T2 a b) -> a + b) $ 
  -- --          zip (reverse $ map (+1) (reverse ys)) $ reverse ys
  -- let Z_ ::. n = shape ys
  -- let f'' = backpermute (Z_ ::. 5 ::. 2) (\(I2 x y) -> I1 (x*y)) ys
  -- let f' = replicate (Z_ ::. All_ ::. n) ys
  -- let f = zip (reverse ys) ys
  -- -- putStrLn $ test @UniformScheduleFun @NativeKernel $ program -- backpermute (Z_ ::. 5) (\x->x) (reverse ys)
  -- -- print $ runN @Native program
  -- print $ runN @Native f
  -- let f = runN @Native program
  -- -- let xs' = f xs
  -- print $ f

  -- putStrLn "generate:"
  -- let f = generate (I1 10) (\(I1 x0) -> 10 :: Exp Int)
  -- -- putStrLn $ test @UniformScheduleFun @NativeKernel f
  -- print $ run @Native f

  -- putStrLn "mapmap:"
  -- let f = map (+1) . map (*2) -- $ ys
  -- -- putStrLn $ test @UniformScheduleFun @NativeKernel f
  -- -- putStrLn $ test @UniformScheduleFun @NativeKernel (f ys)
  -- print $ runN @Native f xs
  -- print $ runN @Native (f ys)

  -- putStrLn "fold:"
  -- let f = fold1 (+) ys
  -- putStrLn $ test @UniformScheduleFun @NativeKernel f
  -- print $ run @Native f

  -- putStrLn "stencil:"
  -- let f = stencil (\(a :: Exp Int,b,c) -> a+b+c) mirror ys
  -- putStrLn $ test @UniformScheduleFun @NativeKernel f
  -- print $ run @Native f

  -- putStrLn "scan:"
  -- let f = scanl1 (+) ys
  -- -- putStrLn $ test @UniformScheduleFun @NativeKernel f
  -- print $ run @Native f

  
 
  -- Prelude.print $ runNWithObj @Native ArrayReadsWrites $ quicksort $ use $ fromList (Z :. 5) [100::Int, 200, 3, 5, 4]
 
----------------------------BENCHMARKS------------------------------
-- complex      from the ILP example
-- complexAdd   a variation on complex, where the results are zipWith-ed together
-- singleLoop   from the introduction
-- diagonal     two maps, fused diagonally
--------------------------------------------------------------------

benchmarkmain = defaultMain $ 
    Prelude.map (benchOption . Prelude.Left) [minBound :: Objective .. maxBound] 
    Prelude.++ 
    Prelude.map (benchOption . Prelude.Right) [NoFusion, GreedyUp, GreedyDown]
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
