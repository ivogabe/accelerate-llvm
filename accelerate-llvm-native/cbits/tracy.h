#include <flag_tracy.h> // provided by accelerate via `install-includes`
#include <string.h>

#ifdef ACCELERATE_TRACY

typedef const void* TracyCZoneCtx;

uint64_t ___tracy_alloc_srcloc( uint32_t line, const char* source, size_t sourceSz, const char* function, size_t functionSz, uint32_t color );
uint64_t ___tracy_alloc_srcloc_name( uint32_t line, const char* source, size_t sourceSz, const char* function, size_t functionSz, const char* name, size_t nameSz, uint32_t color );
TracyCZoneCtx ___tracy_emit_zone_begin_alloc( uint64_t srcloc, int32_t active );
void ___tracy_emit_zone_end( TracyCZoneCtx ctx );
void ___tracy_emit_zone_text( TracyCZoneCtx ctx, const char* txt, size_t size );
void ___tracy_emit_zone_name( TracyCZoneCtx ctx, const char* txt, size_t size );
void ___tracy_emit_zone_color( TracyCZoneCtx ctx, uint32_t color );
void ___tracy_emit_zone_value( TracyCZoneCtx ctx, uint64_t value );
void ___tracy_emit_memory_alloc( const void* ptr, size_t size, int32_t secure );
void ___tracy_emit_memory_free( const void* ptr, int32_t secure );
void ___tracy_emit_memory_alloc_named( const void* ptr, size_t size, int32_t secure, const char* name );
void ___tracy_emit_memory_free_named( const void* ptr, int32_t secure, const char* name );
void ___tracy_emit_message( const char* txt, size_t size, int32_t callstack_depth );
void ___tracy_emit_messageC( const char* txt, size_t size, uint32_t color, int32_t callstack_depth );
void ___tracy_emit_messageL( const char* txt, int32_t callstack_depth );
void ___tracy_emit_messageLC( const char* txt, uint32_t color, int32_t callstack_depth );
void ___tracy_emit_frame_mark( const char* name );
void ___tracy_emit_frame_mark_start( const char* name );
void ___tracy_emit_frame_mark_end( const char* name );
void ___tracy_emit_frame_image( const void* image, uint16_t w, uint16_t h, uint8_t offset, int32_t flip );
void ___tracy_emit_plot( const char* name, double val );
void ___tracy_emit_message_appinfo( const char* txt, size_t size );

#define _CONCAT(a, b) a##b
#define CONCAT(a, b) _CONCAT(a, b)

// TODO: maybe make srcloc static, so we dont need to allocate it every time?
#define TRACY_ZONE_BEGIN(ctx, name, color)  \
  static uint64_t CONCAT(srcloc, __LINE__) = 0; \
  CONCAT(srcloc, __LINE__) = ___tracy_alloc_srcloc(__LINE__, \
                                                   __FILE__, sizeof(__FILE__) - 1, \
                                                   name, strlen(name), \
                                                   color); \
  TracyCZoneCtx ctx = ___tracy_emit_zone_begin_alloc(CONCAT(srcloc, __LINE__), 1)

#define TRACY_ZONE_END(ctx) ___tracy_emit_zone_end(ctx)

#else

#define TRACY_ZONE_BEGIN(ctx, name, color)
#define TRACY_ZONE_END(ctx)

#endif // ACCELERATE_TRACY
