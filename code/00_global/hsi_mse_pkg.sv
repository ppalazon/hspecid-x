`timescale 1ns / 1ps

package hsi_mse_pkg;

  parameter int HM_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
  parameter int HM_DATA_WIDTH_MUL = 32; // Data width for multiplication
  parameter int HM_DATA_WIDTH_ACC = 48; // Data width for accumulator
  parameter int HM_VECTOR_LENGTH_TB = 24; // Length of the vector for testbench
  parameter int HM_LENGTH_BITS = 10; // Number of bits for length
  parameter int HM_BUFFER_LENGTH = 4; // Length of the buffer
  parameter int HM_HSI_BANDS = 128; // Number of bands in HSI
  parameter int HM_HSI_LIBRARY_SIZE = 256; // Size of the HSI library
  parameter int HM_HSI_LIBRARY_SIZE_ADDR = $clog2(HM_HSI_LIBRARY_SIZE); // Number of bits to represent vector length
  parameter int HM_WORD_WIDTH = 32; // Width of the word in bits

endpackage // hsi_mse_pkg.sv