#include "types.h"
#include <unistd.h>

void* accelerate_worker(void* data_packed) {
  struct Workers *workers = accelerate_unpack_ptr((uintptr_t) data_packed);
  uint16_t thread_idx = accelerate_unpack_tag((uintptr_t) data_packed);

  while (true) {
    struct Task task = accelerate_dequeue(workers);
    if (task.program != NULL) {
      task.program->run(workers, task.program, task.location);
    }
    // TODO: Try to assist another task via work assisting
    // TODO: yield, and eventually park this thread and let it be woken via the scheduler.
  }
}

struct Workers* accelerate_start_workers(uint64_t thread_count) {
  struct Workers *workers = malloc(sizeof(struct Workers));

  workers->scheduler.lock = 16;
  workers->scheduler.task_capacity = 32 * 1024;
  workers->scheduler.task_count = 0;
  workers->scheduler.tasks = malloc(sizeof(struct Task) * workers->scheduler.task_capacity);

  workers->thread_count = thread_count;

  for (int i = 0; i < thread_count; i++) {
    // TODO: Check if setting thread affinities helps
    pthread_t worker_thread;
    uintptr_t data = accelerate_pack(workers, i);
    pthread_create(&worker_thread, NULL, accelerate_worker, (void*) data);
  }

  return workers;
}
