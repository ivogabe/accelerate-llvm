#include <stddef.h>
#include "types.h"
#include "accelerate_llvm_native_ffi.h"

_Static_assert(sizeof(struct KernelLaunch) == sizeof(struct AccelerateKernelHeader), "public interface in AccelerateKernelHeader should have same layout");
_Static_assert(offsetof(struct KernelLaunch, work_index) == offsetof(struct AccelerateKernelHeader, work_index), "public interface in AccelerateKernelHeader should have same layout");

struct FFIParallelLoop {
  struct KernelLaunch header;
  void *ctx;
  int64_t n;
  void (*work)(void*, int64_t);
  
  // Synchronization primitives to let main thread wait on all work to be
  // finished
  pthread_mutex_t sync_mutex;
  pthread_cond_t sync_cond;
  bool sync_complete;
};

uint8_t ffi_parallel_loop_work(struct FFIParallelLoop *loop, uint8_t *locks, uint32_t thread_idx, uint32_t max_threads) {
  (void) locks; (void) max_threads; // Not needed

  if (thread_idx == 0xFFFFFFFF) { return 1; }
  if (thread_idx == 0xFFFFFFFE) {
    pthread_mutex_lock(&loop->sync_mutex);
    loop->sync_complete = true;
    pthread_cond_broadcast(&loop->sync_cond);
    pthread_mutex_unlock(&loop->sync_mutex);
    return 0;
  }

  while (true) {
    int64_t i = atomic_fetch_add_explicit(&loop->header.work_index, 1, memory_order_relaxed);
    if (i >= loop->n) { break; }
    loop->work(loop->ctx, i);
  }
  return 0;
}

static const struct ___tracy_source_location_data ffi_srcloc = {
  .name = "Parallel loop in FFI",
  .function = "accelerate_llvm_native_ffi_parallel_loop",
  .file = "ffi.c",
  .line = 0,
  .color = 0xFF00FF,
};

// Utility function for implementers of foreign functions (via ForeignAcc), 
// performing parallel work.
// Restrictions: the loop is executed sequentially if the current thread
// already executes parallel work. It is thus not possible to nest parallel
// loops. This includes the parallel loops in which kernels already run,
// if initialization returns 1.
// It is preferred to use that standard loop, but this function is an
// alternative when the ffi has a non-standard parallel structure, or needs to
// integrate with some library.
//
// Furthermore, this function may only be called from a worker thread of the
// Accelerate runtime.
void accelerate_llvm_native_ffi_parallel_loop(void (*work)(void*, int64_t), void *ctx, int64_t n) {
  bool sequential = false;
  struct Workers *workers = accelerate_worker_workers;
  if (n <= 1) {
    // No need to execute this in parallel
    sequential = true;
  } else if (accelerate_worker_thread_idx == 0xFFFFFFFF) {
    // This is not a worker thread; we cannot execute this in parallel
    sequential = true;
  } else if (accelerate_unpack_ptr(atomic_load_explicit(&workers->scheduler.activities[accelerate_worker_thread_idx], memory_order_acquire)) != NULL) {
    // This worker thread already executes a parallel loop;
    // we cannot nest parallel loops
    sequential = true;
  }

  if (sequential) {
    // Sequential fall-back
    for (int64_t i = 0; i < n; i++) {
      work(ctx, i);
    }
    return;
  }

  // Store info for the parallel loop in the format of kernels in the work
  // assisting scheduler on the stack.
  // We later store a pointer to this object in the activities array of the
  // scheduler.
  // This thread must block until all threads have finished the work of this
  // parallel loop. This is different from regular kernels in the work
  // assisting scheduler. Typically, the starting thread can already start
  // different work if other threads are working on the parallel loop, but
  // this requires the code of the program (between kernels) to be written in a
  // specific way (as a coroutine). accelerate_llvm_native_ffi_parallel_loop
  // is implemented for FFI calls that cannot be written in that way, and uses
  // blocking to fit in the scheduler. This may lower performance a tiny bit,
  // but still allows the FFI operation to run in parallel, on the worker
  // threads we already have.
  struct FFIParallelLoop loop;
  loop.header.work_function = (KernelFunction*) ffi_parallel_loop_work;
  loop.header.program = NULL;
  loop.header.program_continuation = 0;
  atomic_store_explicit(&loop.header.active_threads, 0, memory_order_relaxed);
  atomic_store_explicit(&loop.header.work_index, 0, memory_order_relaxed);
  loop.header.work_per_thread = NULL;
  loop.header.tracy_srcloc = &ffi_srcloc;

  loop.ctx = ctx;
  loop.n = n;
  loop.work = work;
  if (pthread_mutex_init(&loop.sync_mutex, 0) != 0 || pthread_cond_init(&loop.sync_cond, 0) != 0) {
    printf("mutex or cond var init failed\n");
    abort();
  }
  loop.sync_complete = false;

  atomic_store_explicit(&workers->scheduler.activities[accelerate_worker_thread_idx], accelerate_pack(&loop.header, 0), memory_order_release);
  accelerate_parker_wake_all(&workers->scheduler.parker);
  ffi_parallel_loop_work(&loop, NULL, accelerate_worker_thread_idx, workers->thread_count);

  bool is_last = accelerate_task_end_main(workers, accelerate_worker_thread_idx, &loop.header);
  if (is_last) {
    // If this was the last thread to work on the parallel loop, we can
    // directly continue with the remaining work (i.e. return)
  } else {
    // Otherwise we need to wait on another thread
    pthread_mutex_lock(&loop.sync_mutex);
    while (!loop.sync_complete) {
      pthread_cond_wait(&loop.sync_cond, &loop.sync_mutex);
    }
    pthread_mutex_unlock(&loop.sync_mutex);
  }
  pthread_mutex_destroy(&loop.sync_mutex);
  pthread_cond_destroy(&loop.sync_cond);
}
