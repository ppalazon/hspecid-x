`timescale 1ns / 1ps

package hsid_pkg;

  localparam int HSID_WORD_WIDTH = 32; // Width of the word in bits
  localparam int HSID_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
  localparam int HSID_DATA_WIDTH_MUL = 32; // Data width for multiplication (32 bits)
  localparam int HSID_DATA_WIDTH_ACC = 40; // Data width for accumulator
  localparam int HSID_HSP_BANDS_WIDTH = 7; // Number of bits for Hyperspectral Pixels (7 bits - 127 bands)
  localparam int HSID_HSP_LIBRARY_WIDTH = 6; // Numer of bits for Hyperspectral Pixels Library (6 bits - 64 pixels)
  localparam int HSID_FIFO_ADDR_WIDTH = 2; // Number of bits for buffer address (4 entries)

  // HSI MSE library state machine states
  typedef enum logic [3:0] {
    HM_IDLE, HM_CLEAR, HM_CONFIG, HM_ERROR, HM_READ_HSP_CAPTURED,
    HM_COMPUTE_MSE, HM_WAIT_MSE, HM_COMPARE_MSE, HM_DONE
  } hsid_main_state_t;

  typedef enum logic [2:0] {
    OR_IDLE, START_READ_CAPTURED, READ_CAPTURED, START_READ_LIBRARY, READ_LIBRARY
  } hsid_x_obi_read_t;

endpackage