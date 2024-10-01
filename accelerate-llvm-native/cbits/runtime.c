#include "types.h"
#include <unistd.h>
#include <sched.h>

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
  if (atomic_load_explicit(&parker->any_sleeping, memory_order_acquire) == 0) {
    // No thread is sleeping
    return;
  }
  pthread_mutex_lock(&parker->lock);
  atomic_store_explicit(&parker->any_sleeping, 0, memory_order_release);
  pthread_cond_broadcast(&parker->cond_var);
  pthread_mutex_unlock(&parker->lock);
}

#define ATTEMPTS 16

void* accelerate_worker(void *data_packed) {
  struct Workers *workers = accelerate_unpack_ptr((uintptr_t) data_packed);
  uint16_t thread_idx = accelerate_unpack_tag((uintptr_t) data_packed);

  uint attempts_remaining = ATTEMPTS;

  while (true) {
    if (attempts_remaining == 0) {
      accelerate_parker_maybe_park(&workers->scheduler.parker);
    }
    struct Task task = accelerate_dequeue(workers);
    if (task.program != NULL) {
      if (attempts_remaining == 0) {
        accelerate_parker_cancel_park(&workers->scheduler.parker);
      }
      task.program->run(workers, task.program, task.location);
      accelerate_program_release(task.program);
      attempts_remaining = ATTEMPTS;
      continue;
    }
    // TODO: Try to assist another task via work assisting
    if (attempts_remaining == 0) {
      accelerate_parker_confirm_park(&workers->scheduler.parker);
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

  workers->thread_count = thread_count;

  for (uint64_t i = 0; i < thread_count; i++) {
    // TODO: Check if setting thread affinities helps
    pthread_t worker_thread;
    uintptr_t data = accelerate_pack(workers, i);
    pthread_create(&worker_thread, NULL, accelerate_worker, (void*) data);
  }

  return workers;
}
