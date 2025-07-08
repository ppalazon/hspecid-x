// Generated register defines for hsid_x_ctrl

#ifndef _HSID_X_CTRL_REG_DEFS_
#define _HSID_X_CTRL_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Register width
#define HSID_X_CTRL_PARAM_REG_WIDTH 32

// HSpecID-X main control and status register
#define HSID_X_CTRL_STATUS_REG_OFFSET 0x0
#define HSID_X_CTRL_STATUS_START_BIT 0
#define HSID_X_CTRL_STATUS_IDLE_BIT 1
#define HSID_X_CTRL_STATUS_READY_BIT 2
#define HSID_X_CTRL_STATUS_DONE_BIT 3
#define HSID_X_CTRL_STATUS_CLEAR_BIT 4
#define HSID_X_CTRL_STATUS_ERROR_BIT 5

// Amount of reference pixels in memory to compare with captured pixel
#define HSID_X_CTRL_LIBRARY_SIZE_REG_OFFSET 0x4
#define HSID_X_CTRL_LIBRARY_SIZE_LIBRARY_SIZE_MASK 0xfff
#define HSID_X_CTRL_LIBRARY_SIZE_LIBRARY_SIZE_OFFSET 0
#define HSID_X_CTRL_LIBRARY_SIZE_LIBRARY_SIZE_FIELD \
  ((bitfield_field32_t) { .mask = HSID_X_CTRL_LIBRARY_SIZE_LIBRARY_SIZE_MASK, .index = HSID_X_CTRL_LIBRARY_SIZE_LIBRARY_SIZE_OFFSET })

// Number of bands in each pixel
#define HSID_X_CTRL_PIXEL_BANDS_REG_OFFSET 0x8
#define HSID_X_CTRL_PIXEL_BANDS_PIXEL_BANDS_MASK 0xff
#define HSID_X_CTRL_PIXEL_BANDS_PIXEL_BANDS_OFFSET 0
#define HSID_X_CTRL_PIXEL_BANDS_PIXEL_BANDS_FIELD \
  ((bitfield_field32_t) { .mask = HSID_X_CTRL_PIXEL_BANDS_PIXEL_BANDS_MASK, .index = HSID_X_CTRL_PIXEL_BANDS_PIXEL_BANDS_OFFSET })

// Address of the captured pixel in main memory
#define HSID_X_CTRL_CAPTURED_PIXEL_ADDR_REG_OFFSET 0xc

// Address of the first reference pixel in main memory
#define HSID_X_CTRL_LIBRARY_PIXEL_ADDR_REG_OFFSET 0x10

// Reference pixel id from the library with minimum MSE compared to captured
// pixel
#define HSID_X_CTRL_MSE_MIN_REF_REG_OFFSET 0x14

// Reference pixel id from the library with maximum MSE compared to captured
// pixel
#define HSID_X_CTRL_MSE_MAX_REF_REG_OFFSET 0x18

// Minimum MSE value compared to captured pixel
#define HSID_X_CTRL_MSE_MIN_VALUE_REG_OFFSET 0x1c

// Maximum MSE value compared to captured pixel
#define HSID_X_CTRL_MSE_MAX_VALUE_REG_OFFSET 0x20

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _HSID_X_CTRL_REG_DEFS_
// End generated register defines for hsid_x_ctrl
