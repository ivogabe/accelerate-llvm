#ifdef __linux__
// Define this to get access to thread affinities.
// We only set thread affinities on Linux, since macOS does not support this.
#define _GNU_SOURCE
#endif

#include "types.h"
#include "tracy.h"
#include <unistd.h>
#include <sched.h>

struct RuntimeLib accelerate_runtime_lib = (struct RuntimeLib){
  .accelerate_buffer_alloc = accelerate_buffer_alloc,
  .accelerate_buffer_release = accelerate_buffer_release,
  .accelerate_buffer_retain = accelerate_buffer_retain,
  .accelerate_ref_release = accelerate_ref_release,
  .accelerate_ref_retain = accelerate_ref_retain,
  .accelerate_ref_write_buffer = accelerate_ref_write_buffer,
  .accelerate_schedule = accelerate_schedule,
  .accelerate_schedule_after = accelerate_schedule_after,
  .accelerate_schedule_after_or = accelerate_schedule_after_or,
  .accelerate_signal_resolve = accelerate_signal_resolve,
  .hs_try_putmvar = hs_try_putmvar
};

static void accelerate_parker_maybe_park(struct ThreadParker *parker) {
  pthread_mutex_lock(&parker->lock);
  atomic_store_explicit(&parker->any_sleeping, 1, memory_order_release);
}
static void accelerate_parker_confirm_park(struct ThreadParker *parker) {
  pthread_cond_wait(&parker->cond_var, &parker->lock);
  // Note that spurious wakes may happen, but that's not a big problem.
  // We'll just check the queue a few times then, and then park again.
  pthread_mutex_unlock(&parker->lock);
}
static void accelerate_parker_cancel_park(struct ThreadParker *parker) {
  pthread_mutex_unlock(&parker->lock);
  // Note: we cannot change parker->any_sleeping here, as that may prevent other threads from waking up.
}
void accelerate_parker_wake_all(struct ThreadParker *parker) {
  pthread_mutex_lock(&parker->lock);
  // TODO: We need to perform this check inside the critical section to avoid
  // a race condition. However, this does increase lock contention, so ideally
  // we should find a better solution for this. For now, this at least makes it
  // sound.
  if (atomic_load_explicit(&parker->any_sleeping, memory_order_acquire) == 0) {
    // No thread is sleeping
    pthread_mutex_unlock(&parker->lock);
    return;
  }
  atomic_store_explicit(&parker->any_sleeping, 0, memory_order_release);
  pthread_cond_broadcast(&parker->cond_var);
  pthread_mutex_unlock(&parker->lock);
}

// Claims an entry from Workers.work_per_thread_array.
// Note that this claims one array, to be used for scheduling within a kernel.
// It does not claim the actual work within that kernel.
// See comment on Workers.work_per_thread_array
inline _Atomic uint64_t* accelerate_work_per_thread_claim(struct Workers *workers, uint16_t thread_idx) {
  uint16_t thread_count = workers->thread_count;
  int16_t inc = (thread_idx % 2 == 0) ? 1 : (thread_count - 1);
  int16_t i = thread_idx;

  // This loop will terminate, because:
  // Each thread may only 'own' one work_per_thread at a time.
  // There are thread_count work_per_threads.
  // A thread cannot call accelerate_work_per_thread_claim when it already owns
  // one.
  // Hence there will be at least one free entry; we just need to find it.
  // Note that due to concurrent access, which entry is free may change during
  // the execution of the function. We just know that at any point in time, at
  // least one entry will be free.
  while (true) {
    uint16_t slot_idx = i / 64;
    uint16_t bit_idx = i % 64;

    // If this ever becomes a bottleneck, we can optimize this code by using
    // the fact that multiple bits are in one uint64. We can for instance
    // find a free spot directly using count-leading-zeros over the bitwise negated value,
    // instead of individually trying all bits via atomic_fetch_or_explicit.
    uint64_t old = atomic_fetch_or_explicit(&workers->work_per_thread_free[slot_idx], 1 << bit_idx, memory_order_acquire);
    if ((old & (1 << bit_idx)) != 0) {
      return &workers->work_per_thread_array[i * thread_count * ACCELERATE_WORK_PER_THREAD_STRIDE];
    }

    i += inc;
    if (i >= thread_count) i -= thread_count;
  }
}

inline void accelerate_work_per_thread_free(struct Workers *workers, _Atomic uint64_t *work_per_thread) {
  int16_t idx = (work_per_thread - workers->work_per_thread_array) / (workers->thread_count * ACCELERATE_WORK_PER_THREAD_STRIDE);
  uint16_t slot_idx = idx / 64;
  uint16_t bit_idx = idx % 64;
  atomic_fetch_and_explicit(&workers->work_per_thread_free[slot_idx], ~(1 << bit_idx), memory_order_release);
}

#define ATTEMPTS 16

void* accelerate_worker(void *data_packed) {
  struct Workers *workers = accelerate_unpack_ptr((uintptr_t) data_packed);
  uint16_t thread_idx = accelerate_unpack_tag((uintptr_t) data_packed);

  unsigned int attempts_remaining = ATTEMPTS;

#ifdef __linux__
  {
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(thread_idx, &cpuset);

    pthread_t current_thread = pthread_self();    
    pthread_setaffinity_np(current_thread, sizeof(cpu_set_t), &cpuset);
  }
#endif

  struct Task task;
  task.program = NULL;
  task.location = 0;
  while (true) {
    if (attempts_remaining == 0) {
      accelerate_parker_maybe_park(&workers->scheduler.parker);
    }
    if (task.program == NULL) {
      task = accelerate_dequeue(workers);
    }

    if (task.program != NULL) {
      if (attempts_remaining == 0) {
        accelerate_parker_cancel_park(&workers->scheduler.parker);
      }

      TRACY_ZONE_BEGIN(run_ctx, &program_run_srcloc, COLOR_NORMAL);
      struct KernelLaunch* kernel = task.program->run(&accelerate_runtime_lib, workers, thread_idx, task.program, task.location);
      TRACY_ZONE_END(run_ctx);

      if (kernel == NULL) {
        accelerate_program_release(task.program);
        task.program = NULL;
        task.location = 0;
      } else {
        kernel->work_per_thread = accelerate_work_per_thread_claim(workers, thread_idx);
        // Initialize kernel memory and check if the kernel should be executed in parallel.
        TRACY_ZONE_BEGIN(init_ctx, kernel->tracy_srcloc, COLOR_LIGHT);
        unsigned char parallel =
          kernel->work_function(kernel, workers->locks, 0xFFFFFFFF, workers->thread_count);
        TRACY_ZONE_END(init_ctx);

        // start_task from the Work Assisting paper
        if (parallel == 1) {
          atomic_store_explicit(&workers->scheduler.activities[thread_idx], accelerate_pack(kernel, 0), memory_order_release);
          accelerate_parker_wake_all(&workers->scheduler.parker);
        }

        TRACY_ZONE_BEGIN(work_ctx, kernel->tracy_srcloc, COLOR_NORMAL);
        kernel->work_function(kernel, workers->locks, thread_idx, workers->thread_count);
        TRACY_ZONE_END(work_ctx);

        // Keep track of whether this was the last thread working on the kernel
        bool is_last;
        if (parallel == 1) {
          // signal_task_empty from the Work Assisting paper,
          // and end_task
          // Note that in the paper, the work function calls this function.
          // In this implementation, this happens here.
          // This simplifies the code generation for work function (which are compiled via LLVM),
          // and allows us to combine the decrement of active_threads from end_task.
          uintptr_t old = atomic_exchange_explicit(
            &workers->scheduler.activities[thread_idx],
            accelerate_pack(NULL, 0),
            memory_order_relaxed
          );
          if (accelerate_unpack_ptr(old) == kernel) {
            // Move the reference count from the pointer to the task object,
            // and decrement the reference count by one.
            // This combines the atomic_fetch_add in signal_task_empty with the one in end_task
            uint16_t count = accelerate_unpack_tag(old);
            if (count == 0) {
              // No other thread has assisted. No need to update the reference count.
              // Since there is no other thread, we know this is also th last thread.
              is_last = true;
            } else {
              int32_t remaining_threads = atomic_fetch_add_explicit(
                &kernel->active_threads,
                // The + 1 from signal_task_empty cancels out with the -1 in end_task
                count,
                memory_order_acq_rel
              );
              is_last = -remaining_threads == count;
            }
          } else {
            // Decrement active_threads (end_task in the Work Assisting paper)
            int32_t remaining_threads = atomic_fetch_add_explicit(
              &kernel->active_threads,
              -1,
              memory_order_acq_rel
            );
            is_last = remaining_threads == 1;
          }
        } else {
          // This kernel was executed by a single thread, so this is definitely the last thread.
          is_last = true;
        }

        if (is_last) {
          // The last thread executes the finish function.
          // First, execute the finish procedure of the kernel:
          TRACY_ZONE_BEGIN(final_ctx, kernel->tracy_srcloc, COLOR_LIGHT);
          kernel->work_function(kernel, workers->locks, 0xFFFFFFFE, workers->thread_count);
          TRACY_ZONE_END(final_ctx);
          // Recycle work_per_thread for later kernels
          accelerate_work_per_thread_free(workers, kernel->work_per_thread);
          // Then continue the program after this kernel, via
          // program_continuation in the KernelLaunch structure.
          task.program = kernel->program;
          task.location = kernel->program_continuation;
        } else {
          task.program = NULL;
          task.location = 0;
        }
      }
      attempts_remaining = ATTEMPTS;
      continue;
    }

    // Try assisting with the data-parallel activity (KernelLaunch) from another thread.
    // try_assist from the Work Assisting paper
    uint16_t thread_count = workers->thread_count;
    int16_t inc = (thread_idx % 2 == 0) ? 1 : (thread_count - 1);
    int16_t other_thread = thread_idx;
    bool workassisting_found = false;
    while (true) {
      other_thread += inc;
      if (other_thread >= thread_count) other_thread -= thread_count;
      if (other_thread == thread_idx) break;

      _Atomic(uintptr_t) *ptr = &workers->scheduler.activities[other_thread];
      if (atomic_load_explicit(ptr, memory_order_relaxed) == 0) continue;
      uintptr_t activity = atomic_fetch_add_explicit(ptr, accelerate_pack(NULL, 1), memory_order_acquire);
      struct KernelLaunch *kernel = accelerate_unpack_ptr(activity);
      if (kernel == NULL) continue;
      // We found a data-parallel activity where we can assist!
      if (attempts_remaining == 0) {
        accelerate_parker_cancel_park(&workers->scheduler.parker);
      }

      TRACY_ZONE_BEGIN(steal_ctx, kernel->tracy_srcloc, COLOR_DARK);
      kernel->work_function(kernel, workers->locks, thread_idx, workers->thread_count);
      TRACY_ZONE_END(steal_ctx);

      // signal_task_empty from the Work Assisting paper,
      // and end_task
      // Similar to above, signal_task_empty happens here instead of in the work function.
      // The same reasoning as above applies here.
      uintptr_t old = atomic_load_explicit(ptr, memory_order_relaxed);
      bool is_last;
      while (true) {
        if (accelerate_unpack_ptr(old) != kernel) {
          // Another thread has moved the reference count.
          // We now only need to decrement the reference count for this thread.
          int32_t remaining_threads = atomic_fetch_add_explicit(
            &kernel->active_threads,
            -1,
            memory_order_acq_rel
          );
          is_last = remaining_threads == 1;
          break;
        }
        if (atomic_compare_exchange_weak_explicit(ptr, &old, accelerate_pack(NULL, 0), memory_order_relaxed, memory_order_relaxed)) {
          // Move the reference count from the pointer to the task object.
          int32_t remaining_threads = atomic_fetch_add_explicit(&kernel->active_threads, accelerate_unpack_tag(old), memory_order_acq_rel);
          is_last = -remaining_threads == accelerate_unpack_tag(old);
          break;
        }
      }
      if (is_last) {
        // The last thread executes the finish function.
        // First, execute the finish procedure of the kernel:
        TRACY_ZONE_BEGIN(final_ctx, kernel->tracy_srcloc, COLOR_DARK);
        kernel->work_function(kernel, workers->locks, 0xFFFFFFFE, workers->thread_count);
        TRACY_ZONE_END(final_ctx);
        // Recycle work_per_thread for later kernels
        accelerate_work_per_thread_free(workers, kernel->work_per_thread);
        // Then continue the program after this kernel, via
        // program_continuation in the KernelLaunch structure.
        task.program = kernel->program;
        task.location = kernel->program_continuation;
      }
      attempts_remaining = ATTEMPTS;
      workassisting_found = true;
      break;
    }
    if (workassisting_found) continue;

    // No task or data-parallel activity available.
    if (attempts_remaining == 0) {
      accelerate_parker_confirm_park(&workers->scheduler.parker);
      attempts_remaining = ATTEMPTS;
    } else {
      if (attempts_remaining < ATTEMPTS / 2) {
        sched_yield();
      }
      attempts_remaining -= 1;
    }
  }
}

struct Workers* accelerate_start_workers(uint64_t thread_count) {
  struct Workers *workers = malloc(sizeof(struct Workers));

  workers->scheduler.queue = accelerate_queue_new();
  if (pthread_mutex_init(&workers->scheduler.parker.lock, NULL) != 0) {
    perror("Accelerate runtime: could not initialize mutex.");                                        
    exit(1);      
  }
  if (pthread_cond_init(&workers->scheduler.parker.cond_var, NULL) != 0) {                                    
    perror("Accelerate runtime: could not initialize pthread cond var.");                                        
    exit(1);                                                                    
  }

  workers->scheduler.activities = calloc(thread_count, sizeof(uintptr_t));

  workers->thread_count = thread_count;

  // ACCELERATE_LOCK_ARRAY_SIZE is measured in bits, convert to bytes.
  workers->locks = calloc(ACCELERATE_LOCK_ARRAY_SIZE / 8, 1);

  workers->work_per_thread_array = calloc(thread_count * thread_count * ACCELERATE_WORK_PER_THREAD_STRIDE, sizeof(uint64_t));
  workers->work_per_thread_free = calloc((thread_count + 63) / 64, sizeof(uint64_t));

  for (uint64_t i = 0; i < thread_count; i++) {
    // TODO: Check if setting thread affinities helps
    pthread_t worker_thread;
    uintptr_t data = accelerate_pack(workers, i);
    pthread_create(&worker_thread, NULL, accelerate_worker, (void*) data);
  }

  return workers;
}
