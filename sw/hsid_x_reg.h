// Generated register defines for hsid_x

#ifndef _HSID_X_REG_DEFS_
#define _HSID_X_REG_DEFS_

#ifdef __cplusplus
extern "C"
{
#endif
// Register width
#define HSID_X_PARAM_REG_WIDTH 32

// HSpecID-X main control and status register
#define HSID_X_CONTROL_REG_OFFSET 0x0
#define HSID_X_CONTROL_START_BIT 0
#define HSID_X_CONTROL_IDLE_BIT 1
#define HSID_X_CONTROL_READY_BIT 2
#define HSID_X_CONTROL_DONE_BIT 3
#define HSID_X_CONTROL_CLEAR_BIT 4

// Amount of reference pixels in memory to compare with captured pixel
#define HSID_X_LIBRARY_SIZE_REG_OFFSET 0x4

// Number of bands in each pixel
#define HSID_X_PIXEL_BANDS_REG_OFFSET 0x8

// Address of the captured pixel in main memory
#define HSID_X_CAPTURED_PIXEL_ADDR_REG_OFFSET 0xc

// Address of the first reference pixel in main memory
#define HSID_X_LIBRARY_PIXEL_ADDR_REG_OFFSET 0x10

// Reference pixel id from the library with minimum MSE compared to captured
// pixel
#define HSID_X_MSE_MIN_REF_REG_OFFSET 0x14

// Reference pixel id from the library with maximum MSE compared to captured
// pixel
#define HSID_X_MSE_MAX_REF_REG_OFFSET 0x18

// Minimum MSE value compared to captured pixel
#define HSID_X_MSE_MIN_VALUE_REG_OFFSET 0x1c

// Maximum MSE value compared to captured pixel
#define HSID_X_MSE_MAX_VALUE_REG_OFFSET 0x20

#ifdef __cplusplus
} // extern "C"
#endif
#endif // _HSID_X_REG_DEFS_
// End generated register defines for hsid_x
