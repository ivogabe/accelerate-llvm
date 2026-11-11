#include "types.h"
#include "tracy.h"

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
    pthread_mutex_unlock(&loop->sync_mutex);
    pthread_cond_broadcast(&loop->sync_cond);
    return 0;
  }

  while (true) {
    int64_t i = atomic_fetch_add_explicit(&loop->header.work_index, 1, memory_order_relaxed);
    if (i >= loop->n) { break; }
    loop->work(loop->ctx, i);
  }
  return 0;
}

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
  if (n == 1) {
    // No need to execute this in parallel
    sequential = true;
  } else if (accelerate_worker_thread_idx == 0xFFFFFFFF) {
    // This is not a worker thread; we cannot execute this in parallel
    sequential = true;
  } else if (atomic_load_explicit(&workers->scheduler.activities[accelerate_worker_thread_idx], memory_order_acquire) != 0) {
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

  struct FFIParallelLoop loop;
  loop.header.work_function = (KernelFunction*) ffi_parallel_loop_work;
  loop.header.program = NULL;
  loop.header.program_continuation = 0;
  atomic_store_explicit(&loop.header.active_threads, 0, memory_order_relaxed);
  atomic_store_explicit(&loop.header.work_index, 0, memory_order_relaxed);
  loop.header.work_per_thread = NULL;
  loop.header.tracy_srcloc = NULL;

  loop.ctx = ctx;
  loop.n = n;
  loop.work = work;
  if (pthread_mutex_init(&loop.sync_mutex, 0) != 0 || pthread_cond_init(&loop.sync_cond, 0)) {
    printf("mutex or cond var init failed\n");
    abort();
  }
  loop.sync_complete = false;

  atomic_store_explicit(&workers->scheduler.activities[accelerate_worker_thread_idx], accelerate_pack(&loop.header, 0), memory_order_release);
  accelerate_parker_wake_all(&workers->scheduler.parker);
  ffi_parallel_loop_work(&loop, NULL, accelerate_worker_thread_idx, workers->thread_count);

  uintptr_t old = atomic_exchange_explicit(
    &workers->scheduler.activities[accelerate_worker_thread_idx],
    accelerate_pack(NULL, 0),
    memory_order_relaxed
  );
  bool is_last;
  if (accelerate_unpack_ptr(old) == &loop.header) {
    // Move the reference count from the pointer to the task object,
    // and decrement the reference count by one.
    // This combines the atomic_fetch_add in signal_task_empty with the one in end_task
    uint16_t count = accelerate_unpack_tag(old);
    if (count == 0) {
      // No other thread has assisted. No need to update the reference count.
      // Since there is no other thread, we know this is also the last thread.
      is_last = true;
    } else {
      int32_t remaining_threads = atomic_fetch_add_explicit(
        &loop.header.active_threads,
        // The + 1 from signal_task_empty cancels out with the -1 in end_task
        count,
        memory_order_acq_rel
      );
      is_last = -remaining_threads == count;
    }
  } else {
    // Decrement active_threads (end_task in the Work Assisting paper)
    int32_t remaining_threads = atomic_fetch_add_explicit(
      &loop.header.active_threads,
      -1,
      memory_order_acq_rel
    );
    is_last = remaining_threads == 1;
  }
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
}
