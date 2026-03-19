#include <flag_tracy.h> // provided by accelerate via `install-includes`
#include <string.h>
#include <stdlib.h>

#ifdef ACCELERATE_TRACY

struct ___tracy_source_location_data
{
    const char* name;
    const char* function;
    const char* file;
    uint32_t line;
    uint32_t color;
};

typedef const void* TracyCZoneCtx;

TracyCZoneCtx ___tracy_emit_zone_begin(const struct ___tracy_source_location_data* srcloc, int32_t active);
void ___tracy_emit_zone_end(TracyCZoneCtx ctx);
void ___tracy_emit_zone_color(TracyCZoneCtx ctx, uint32_t color);

typedef enum {
  COLOR_DARK,
  COLOR_NORMAL,
  COLOR_LIGHT,
} ColorVariant;

uint32_t get_color_variant(uint32_t color, ColorVariant variant);

#define _CONCAT(a, b) a##b
#define CONCAT(a, b) _CONCAT(a, b)

#define TRACY_ZONE_BEGIN(ctx, tracy_srcloc, color_variant)  \
  TracyCZoneCtx ctx = ___tracy_emit_zone_begin(tracy_srcloc, 1); \
  ___tracy_emit_zone_color(ctx, get_color_variant(tracy_srcloc->color, color_variant))

#define TRACY_ZONE_END(ctx) ___tracy_emit_zone_end(ctx)

uint32_t min(uint32_t a, uint32_t b) { return a < b ? a : b; }

uint32_t get_color_variant(uint32_t color, ColorVariant variant) {
  uint32_t r = (color >> 16) & 0xFF;
  uint32_t g = (color >> 8)  & 0xFF;
  uint32_t b = color         & 0xFF;

  switch (variant) {
    case COLOR_DARK:
      r = (r * 2) / 5;
      g = (g * 2) / 5;
      b = (b * 2) / 5;
      break;

    case COLOR_NORMAL:
      break;

    case COLOR_LIGHT:
      r = min((r * 7) / 5, 0xFF);
      g = min((g * 7) / 5, 0xFF);
      b = min((b * 7) / 5, 0xFF);
      break;
  }

  return ((r & 0xFF) << 16) |
         ((g & 0xFF) << 8)  |
         ((b & 0xFF));
}

#else

#define TRACY_ZONE_BEGIN(ctx, name, color)
#define TRACY_ZONE_END(ctx)

#endif // ACCELERATE_TRACY
