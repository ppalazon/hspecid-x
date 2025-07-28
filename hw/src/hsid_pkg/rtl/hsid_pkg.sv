`timescale 1ns / 1ps

package hsid_pkg;

  localparam int HSID_WORD_WIDTH = 32; // Width of the word in bits
  localparam int HSID_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
  localparam int HSID_DATA_WIDTH_MUL = HSID_DATA_WIDTH * 2; // Data width for multiplication
  localparam int HSID_DATA_WIDTH_ACC = HSID_DATA_WIDTH * 3; // Data width for accumulator
  localparam int HSID_HSP_BANDS_WIDTH = 8; // Number of bits for Hyperspectral Pixels (8 bits - 256 bands)
  localparam int HSID_HSP_LIBRARY_WIDTH = 11 ; // Numer of bits for Hyperspectral Pixels Library (11 bits - 4096 pixels)
  localparam int HSID_BUFFER_WIDTH = 2; // Number of bits for buffer address (4 entries)

  // Test parameters
  localparam int HSID_TEST_BANDS = 16; // Number of HSP bands to test
  localparam int HSID_TEST_LIBRARY_SIZE = 10; // Size of the HSI library to test
  localparam int HSID_TEST_BAND_PACKS = HSID_TEST_BANDS / 2; // Number of band packs in the vector for testbench

  // HSI MSE library state machine states
  typedef enum logic [2:0] {
    IDLE, READ_MEASURE, COMPUTE_MSE, WAIT_MSE, COMPARE_MSE, DONE
  } hsid_main_state_t;

  typedef enum logic [2:0] {
    OR_IDLE, START_READ_CAPTURED, READ_CAPTURED, START_READ_LIBRARY, READ_LIBRARY
  } hsid_x_obi_read_t;

endpackage