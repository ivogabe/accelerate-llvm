#include <cinttypes>
#include <atomic>

// Should be in sync with ThreadParker in ./types.h (that file is not included here to prevent C vs C++ issues)
struct ThreadParker {
  std::atomic<std::uint64_t> state; // Internal state, incremented for each wake()
  std::atomic<std::uint64_t> any_sleeping; // Non-zero when at least one thread is sleeping
  std::atomic<std::uint64_t> count_sleeping; // Number of sleeping threads

  // Note that any_sleeping and count_sleeping can be contradictory. When
  // waking all threads, we directly set any_sleeping to false (zero), but
  // count_sleeping is only updated later on by the thread itself. this only
  // happens when the thread is actually active. We use these two separate
  // methods to determine whether threads are active, since:
  // 1. any_sleeping is accurate after accelerate_parker_wake_all
  // 2. accelerate_parker_wake_one cannot update any_sleeping, but will
  //    (eventually, when the thread wakes) update count_sleeping.
  // Hence we (eventually) have accurate information, both for wake_one-heavy
  // and for wake_all-heavy programs.
};

extern "C" {
  std::uint64_t accelerate_parker_maybe_park(ThreadParker *parker) {
    parker->any_sleeping.store(1, std::memory_order_release);
    parker->count_sleeping.fetch_add(1, std::memory_order_acq_rel);
    return parker->state.load(std::memory_order_acquire);
  }
  void accelerate_parker_confirm_park(ThreadParker *parker, std::uint64_t value) {
    parker->state.wait(value, std::memory_order_acquire);
    parker->count_sleeping.fetch_sub(1, std::memory_order_acq_rel);
  }
  void accelerate_parker_cancel_park(ThreadParker *parker) {
    parker->count_sleeping.fetch_sub(1, std::memory_order_acq_rel);
  }
  void accelerate_parker_wake_one(ThreadParker *parker) {
    if (parker->any_sleeping.load(std::memory_order_acquire) == 0 || parker->count_sleeping.load(std::memory_order_acquire) == 0) {
      // No sleeping threads, no need to wake any threads
      return;
    }
    // Update state, so .wait can unblock
    parker->state.fetch_add(1, std::memory_order_release);
    // Notify one thread
    parker->state.notify_one();
  }
  void accelerate_parker_wake_all(ThreadParker *parker) {
    if (parker->any_sleeping.load(std::memory_order_acquire) == 0 || parker->count_sleeping.load(std::memory_order_acquire) == 0) {
      // No sleeping threads, no need to wake any threads
      return;
    }
    parker->any_sleeping.store(0, std::memory_order_release);
    // Update state, so .wait can unblock
    parker->state.fetch_add(1, std::memory_order_release);
    // Notify all waiting threads
    parker->state.notify_all();
  }
}
