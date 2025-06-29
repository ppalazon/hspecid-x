`timescale 1ns / 1ps

package hsi_mse_pkg;

  localparam int HM_WORD_WIDTH = 32; // Width of the word in bits
  localparam int HM_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
  localparam int HM_DATA_WIDTH_MUL = HM_DATA_WIDTH * 2; // Data width for multiplication
  localparam int HM_DATA_WIDTH_ACC = HM_DATA_WIDTH * 3; // Data width for accumulator
  localparam int HM_VECTOR_LENGTH_TB = 24; // Length of the vector for testbench
  localparam int HM_LENGTH_BITS = 10; // Number of bits for length
  localparam int HM_BUFFER_LENGTH = 4; // Length of the buffer
  localparam int HM_HSI_BANDS = 128; // Number of bands in HSI
  localparam int HM_HSI_LIBRARY_SIZE = 256; // Size of the HSI library
  localparam int HM_DATA_PER_WORD = HM_WORD_WIDTH / HM_DATA_WIDTH; // Number of data elements per word

  typedef enum logic [2:0] {
    IDLE, READ_MEASURE, COMPUTE_MSE, WAIT_MSE, COMPARE_MSE, DONE
  } hsi_mse_lib_state_t;

endpackage // hsi_mse_pkg.sv