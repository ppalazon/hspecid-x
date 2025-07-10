`timescale 1ns / 1ps

package hsid_pkg;

  localparam int HSID_WORD_WIDTH = 32; // Width of the word in bits
  localparam int HSID_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
  localparam int HSID_DATA_WIDTH_MUL = HSID_DATA_WIDTH * 2; // Data width for multiplication
  localparam int HSID_DATA_WIDTH_ACC = HSID_DATA_WIDTH * 3; // Data width for accumulator
  localparam int HSID_VECTOR_LENGTH_TB = 24; // Length of the vector for testbench
  localparam int HSID_LENGTH_BITS = 10; // Number of bits for length
  localparam int HSID_BUFFER_LENGTH = 4; // Length of the buffer
  localparam int HSID_MAX_HSP_BANDS = 255; // Number of bands in HSI (8 bits)
  localparam int HSID_MAX_HSP_LIBRARY = 4095 ; // Size of the HSI library (11 bits)
  localparam int HSID_DATA_PER_WORD = HSID_WORD_WIDTH / HSID_DATA_WIDTH; // Number of data elements per word

  // Test parameters
  localparam int HSID_TEST_BANDS = 16; // Number of HSI bands to test
  localparam int HSID_TEST_LIBRARY_SIZE = 10; // Size of the HSI library to test
  localparam int HSID_TEST_ELEMENTS = HSID_TEST_BANDS / 2; // Number of elements in the vector for testbench

  // HSI MSE library state machine states
  typedef enum logic [2:0] {
    IDLE, READ_MEASURE, COMPUTE_MSE, WAIT_MSE, COMPARE_MSE, DONE
  } hsid_main_state_t;

endpackage