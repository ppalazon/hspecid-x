`timescale 1ns / 1ps

module hsi_mse #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    parameter HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)  // Number of bits to represent vector length
  ) (
    input logic clk,
    input logic rst_n,

    // Input data for measured HSI vector
    input logic sample_in_en,  // Enable input sample data
    input logic [WORD_WIDTH-1:0] sample_in, // Input sample word data
    output logic sample_in_full,  // Full signal for sample input FIFO

    // Input data for reference hsi vector
    input logic ref_in_en,
    input logic [WORD_WIDTH-1:0] ref_in,
    output logic ref_in_full,

    // Input parameters for the HSI library
    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] library_lenght_in,  // Length of the vectors

    // Output parameters with the MSE result
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] ref_id_out,  // Reference ID of the best match
    output logic [DATA_WIDTH-1:0] mse_out,  // Mean Squared Error output

    // Standard block interface handshake signals
    input  logic start,
    output logic done,
    output logic idle,
    output logic ready
  );

  typedef enum logic [1:0] {
    IDLE, COMPUTE, DONE
  } state_t;
  // State machine parameters
  state_t current_state = IDLE, next_state = COMPUTE;

endmodule