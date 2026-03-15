#include <flag_tracy.h> // provided by accelerate via `install-includes`
#include <string.h>

#ifdef ACCELERATE_TRACY

typedef const void* TracyCZoneCtx;

uint64_t ___tracy_alloc_srcloc(uint32_t line, const char* source, size_t sourceSz, const char* function, size_t functionSz, uint32_t color);
TracyCZoneCtx ___tracy_emit_zone_begin_alloc(uint64_t srcloc, int32_t active);
void ___tracy_emit_zone_end(TracyCZoneCtx ctx);

#define _CONCAT(a, b) a##b
#define CONCAT(a, b) _CONCAT(a, b)

#define TRACY_ZONE_BEGIN(ctx, name, color)  \
  uint64_t CONCAT(srcloc, __LINE__) = ___tracy_alloc_srcloc( \
    __LINE__, \
    __FILE__, sizeof(__FILE__) - 1, \
    name, strlen(name), \
    color \
  ); \
  TracyCZoneCtx ctx = ___tracy_emit_zone_begin_alloc(CONCAT(srcloc, __LINE__), 1)

#define TRACY_ZONE_END(ctx) ___tracy_emit_zone_end(ctx)

#else

#define TRACY_ZONE_BEGIN(ctx, name, color)
#define TRACY_ZONE_END(ctx)

#endif // ACCELERATE_TRACY
