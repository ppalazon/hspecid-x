`timescale 1ns / 1ps

package hsid_pkg;

  localparam int HSID_WORD_WIDTH = 32; // Width of the word in bits
  localparam int HSID_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
  localparam int HSID_DATA_WIDTH_MUL = 32; // Data width for multiplication (32 bits)
  localparam int HSID_DATA_WIDTH_ACC = 40; // Data width for accumulator
  localparam int HSID_HSP_BANDS_WIDTH = 7; // Number of bits for Hyperspectral Pixels (7 bits - 127 bands)
  localparam int HSID_HSP_LIBRARY_WIDTH = 6; // Numer of bits for Hyperspectral Pixels Library (6 bits - 64 pixels)
  localparam int HSID_FIFO_ADDR_WIDTH = 2; // Number of bits for buffer address (4 entries)
  localparam int HSID_MEM_ACCESS_WIDTH = HSID_HSP_BANDS_WIDTH + HSID_HSP_LIBRARY_WIDTH; // Number of bits for addressable memory with pixels

  // HSI MSE library state machine states
  typedef enum logic [3:0] {
    HM_IDLE, HM_CLEAR, HM_CONFIG, HM_ERROR, HM_READ_HSP_CAPTURED,
    HM_COMPUTE_MSE, HM_WAIT_MSE, HM_COMPARE_MSE, HM_DONE
  } hsid_main_state_t;

  // HSID X Top state machine states
  typedef enum logic [3:0] {
    HXT_IDLE, HXT_CLEAR, HXT_CONFIG, HXT_START_READ_CAPTURED, HXT_READ_CAPTURED, HXT_START_READ_LIBRARY, HXT_READ_LIBRARY
  } hsid_x_top_t;

  // HSI OBI memory controller state machine states
  typedef enum logic [2:0] {
    HXOM_IDLE, HXOM_INIT, HXOM_READING, HXOM_DONE, HXOM_CLEAR
  } hsid_x_obi_mem_state_t;

  // Iterative divider state machine states
  typedef enum logic [2:0] {
    HID_IDLE, HID_COMPUTE, HID_CHECK, HID_DONE, HID_CLEAR
  } hsid_ite_div_state_t;

endpackage