// C wrapper around the concurrent queue by Cameron Desrochers
// from https://github.com/cameron314/concurrentqueue,
// stored in concurrentqueue/concurrentqueue.h

#include "concurrentqueue/concurrentqueue.h"

// Should be in sync with Task in ./types.h (that file is not included here to prevent C vs C++ issues)
struct Task {
  void* program;
  uint location;
};
typedef moodycamel::ConcurrentQueue<Task> Queue;

extern "C" {
  Queue* accelerate_queue_new() {
    return new Queue;
  }
  bool accelerate_queue_enqueue(Queue *queue, Task task) {
    return queue->enqueue(task);
  }
  Task accelerate_queue_dequeue(Queue *queue) {
    Task task;
    task.program = NULL;
    task.location = 0;
    queue->try_dequeue(task);
    return task;
  }
  // TODO: Add variants with token arguments
}
