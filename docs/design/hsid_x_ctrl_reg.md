## Summary

| Name                                                      | Offset | Length | Description                                                                     |
| :-------------------------------------------------------- | :----- | -----: | :------------------------------------------------------------------------------ |
| hsid_x_ctrl.[`STATUS`](#status)                           | 0x0    |      4 | HSpecID-X main control and status register                                      |
| hsid_x_ctrl.[`LIBRARY_SIZE`](#library_size)               | 0x4    |      4 | Amount of reference pixels in memory to compare with captured pixel             |
| hsid_x_ctrl.[`PIXEL_BANDS`](#pixel_bands)                 | 0x8    |      4 | Number of bands in each pixel                                                   |
| hsid_x_ctrl.[`CAPTURED_PIXEL_ADDR`](#captured_pixel_addr) | 0xc    |      4 | Address of the captured pixel in main memory                                    |
| hsid_x_ctrl.[`LIBRARY_PIXEL_ADDR`](#library_pixel_addr)   | 0x10   |      4 | Address of the first reference pixel in main memory                             |
| hsid_x_ctrl.[`MSE_MIN_REF`](#mse_min_ref)                 | 0x14   |      4 | Reference pixel id from the library with minimum MSE compared to captured pixel |
| hsid_x_ctrl.[`MSE_MAX_REF`](#mse_max_ref)                 | 0x18   |      4 | Reference pixel id from the library with maximum MSE compared to captured pixel |
| hsid_x_ctrl.[`MSE_MIN_VALUE`](#mse_min_value)             | 0x1c   |      4 | Minimum MSE value compared to captured pixel                                    |
| hsid_x_ctrl.[`MSE_MAX_VALUE`](#mse_max_value)             | 0x20   |      4 | Maximum MSE value compared to captured pixel                                    |

## STATUS
HSpecID-X main control and status register

- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

wavedrom(
{"reg": [{"name": "START", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"name": "IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "READY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DONE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CLEAR", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"name": "ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CANCELLED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
)

| Bits  | Type  | Reset | Name      | Description                                                                                                                                                                                                                            |
| :---: | :---: | :---: | :-------- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 31:7  |       |       |           | Reserved                                                                                                                                                                                                                               |
|   6   |  ro   |  0x0  | CANCELLED | When this bit is set to one, user has clear HSpecID-X during its operations. It will be set to 0 after software reads the register. Default: 0.                                                                                        |
|   5   |  ro   |  0x0  | ERROR     | When this bit is set to one, HSpecID-X has detected an error during its operations. It will be set to 0 after software reads the register. Default: 0.                                                                                 |
|   4   | rw1s  |  0x0  | CLEAR     | When this bit is set to one, HSpecID-X finishes its operations and abort the result. It will be set to 0 after aborting process. Default: 0.                                                                                           |
|   3   |  ro   |  0x0  | DONE      | When this bit is set to one, HSpecID-X is done and software can read output registers to know the results of the HSpecID-X operations. Default: 0.                                                                                     |
|   2   |  ro   |  0x0  | READY     | When this bit is set to one, HSpecID-X is ready and working. Default: 0.                                                                                                                                                               |
|   1   |  ro   |  0x0  | IDLE      | When this bit is set to one, HSpecID-X is idle and it waits for start command. Default: 0.                                                                                                                                             |
|   0   | rw1s  |  0x0  | START     | When this bit is set to 1 by software, HSpecID-X is enabled and starts reading captured pixel and comparing with all reference pixels in memory. It will set to 0 once it's detected by the module and starts the process. Default: 0. |

## LIBRARY_SIZE
Amount of reference pixels in memory to compare with captured pixel

- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

wavedrom(
{"reg": [{"name": "LIBRARY_SIZE", "bits": 6, "attr": ["rw"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
)

| Bits  | Type  | Reset | Name         | Description                                                          |
| :---: | :---: | :---: | :----------- | :------------------------------------------------------------------- |
| 31:6  |       |       |              | Reserved                                                             |
|  5:0  |  rw   |  0x0  | LIBRARY_SIZE | Amount of reference pixels in memory to compare with captured pixel. |

## PIXEL_BANDS
Number of bands in each pixel

- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

wavedrom(
{"reg": [{"name": "PIXEL_BANDS", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name        | Description                    |
| :---: | :---: | :---: | :---------- | :----------------------------- |
| 31:7  |       |       |             | Reserved                       |
|  6:0  |  rw   |  0x0  | PIXEL_BANDS | Number of bands in each pixel. |

## CAPTURED_PIXEL_ADDR
Address of the captured pixel in main memory

- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

wavedrom(
{"reg": [{"name": "CAPTURED_PIXEL_ADDR", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name                | Description                                   |
| :---: | :---: | :---: | :------------------ | :-------------------------------------------- |
| 31:0  |  rw   |  0x0  | CAPTURED_PIXEL_ADDR | Address of the captured pixel in main memory. |

## LIBRARY_PIXEL_ADDR
Address of the first reference pixel in main memory

- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

wavedrom(
{"reg": [{"name": "LIBRARY_PIXEL_ADDR", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name               | Description                                          |
| :---: | :---: | :---: | :----------------- | :--------------------------------------------------- |
| 31:0  |  rw   |  0x0  | LIBRARY_PIXEL_ADDR | Address of the first reference pixel in main memory. |

## MSE_MIN_REF
Reference pixel id from the library with minimum MSE compared to captured pixel

- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

wavedrom(
{"reg": [{"name": "MSE_MIN_REF", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name        | Description                                                                      |
| :---: | :---: | :---: | :---------- | :------------------------------------------------------------------------------- |
| 31:0  |  ro   |  0x0  | MSE_MIN_REF | Reference pixel id from the library with minimum MSE compared to captured pixel. |

## MSE_MAX_REF

Reference pixel id from the library with maximum MSE compared to captured pixel

- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

wavedrom(
{"reg": [{"name": "MSE_MAX_REF", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name        | Description                                                                      |
| :---: | :---: | :---: | :---------- | :------------------------------------------------------------------------------- |
| 31:0  |  ro   |  0x0  | MSE_MAX_REF | Reference pixel id from the library with maximum MSE compared to captured pixel. |

## MSE_MIN_VALUE

Minimum MSE value compared to captured pixel

- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

wavedrom(
{"reg": [{"name": "MSE_MIN_VALUE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name          | Description                                   |
| :---: | :---: | :---: | :------------ | :-------------------------------------------- |
| 31:0  |  ro   |  0x0  | MSE_MIN_VALUE | Minimum MSE value compared to captured pixel. |

## MSE_MAX_VALUE
Maximum MSE value compared to captured pixel

- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

wavedrom(
{"reg": [{"name": "MSE_MAX_VALUE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
)

| Bits  | Type  | Reset | Name          | Description                                   |
| :---: | :---: | :---: | :------------ | :-------------------------------------------- |
| 31:0  |  ro   |  0x0  | MSE_MAX_VALUE | Maximum MSE value compared to captured pixel. |

