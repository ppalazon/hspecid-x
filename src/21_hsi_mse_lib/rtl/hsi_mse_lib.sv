`timescale 1ns / 1ps

import hsi_mse_pkg::*;  // Import the package for HSI MSE

module hsi_mse_lib #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter BUFFER_LENGTH = 4,  // Number of entries in the FIFO buffer
    parameter ELEMENTS = HSI_BANDS / 2, // Number of elements in the vector
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    parameter HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)  // Number of bits to represent vector length
  ) (
    input logic clk,
    input logic rst_n,

    // Input vector data
    input logic hsi_vctr_in_valid,  // Enable input sample data
    input logic [WORD_WIDTH-1:0] hsi_vctr_in, // Input sample word data

    // Input parameters for the HSI library
    input logic [HSI_LIBRARY_SIZE_ADDR:0] library_size_in,  // Amount of HSI library vectors to process

    // Output parameters with the MSE result
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref,
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref,
    output logic [WORD_WIDTH-1:0] mse_min_value,  // Mean Squared Error output
    output logic [WORD_WIDTH-1:0] mse_max_value,  // Mean Squared Error output

    // Clear signal to reset MSE values
    input  logic clear,  // Clear signal to reset MSE values

    // Standard block interface handshake signals
    input  logic start,
    output logic done,
    output logic idle,
    output logic ready
  );

  wire hsi_mse_lib_state_t state;
  wire fifo_measure_full, fifo_measure_empty;
  wire fifo_ref_full, fifo_ref_empty;

  wire [WORD_WIDTH-1:0] fifo_measure_data_in;
  wire fifo_measure_write_en, fifo_ref_write_en;
  wire fifo_both_read_en;

  wire [WORD_WIDTH-1:0] fifo_measure_data_out, fifo_ref_data_out;

  wire mse_valid;  // MSE valid signal
  wire mse_comparison_valid;  // MSE valid signal
  wire element_start;  // Start vector processing signal
  wire element_last;  // Last vector processing signal
  wire element_valid; // Element valid signal
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] vctr_ref;  // Reference vector for MSE
  wire [WORD_WIDTH-1:0] mse_out;  // Mean Squared Error
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_ref;  // Reference vector for MSE


  // Assigns statements
  assign fifo_measure_data_in = (state == READ_MEASURE) ? hsi_vctr_in : (state == COMPUTE_MSE ? fifo_measure_data_out : '0);
  assign fifo_measure_write_en = (state == READ_MEASURE && hsi_vctr_in_valid) || (state == COMPUTE_MSE && !fifo_measure_empty);
  assign fifo_ref_write_en = (state == COMPUTE_MSE && hsi_vctr_in_valid);

  hsi_mse_lib_fsm #(
    .HSI_BANDS(HSI_BANDS),
    .ELEMENTS(ELEMENTS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) fsm (
    .clk(clk),
    .rst_n(rst_n),
    .hsi_library_size(library_size_in),
    .fifo_measure_full(fifo_measure_full),
    .fifo_measure_empty(fifo_measure_empty),
    .fifo_ref_empty(fifo_ref_empty),
    .fifo_ref_full(fifo_ref_full),
    .msi_valid(mse_valid),  // MSE valid signal
    .msi_comparison_valid(mse_comparison_valid),  // MSE comparison valid signal
    .state(state),
    .vctr_count(vctr_ref),  // Not used in this module
    .element_start(element_start),  // Start vector processing signal
    .element_last(element_last),
    .element_valid(element_valid),
    .vctr_last(),  // Library finished signal
    .fifo_both_read_en(fifo_both_read_en),  // FIFO read enable signal
    .start(start),
    .done(done),
    .idle(idle),
    .ready(ready)
  );

  hsi_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .HSI_BANDS(HSI_BANDS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) hsi_mse (
    .clk(clk),
    .rst_n(rst_n),
    .element_start(element_start),
    .element_last(element_last),
    .vctr_ref(vctr_ref),
    .element_a(fifo_measure_data_out),
    .element_b(fifo_ref_data_out),
    .element_valid(element_valid),
    .mse_value(mse_out),
    .mse_ref(mse_ref),
    .mse_valid(mse_valid)
  );

  hsi_mse_comp #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) hsi_mse_comp (
    .clk(clk),
    .rst_n(rst_n),
    .mse_in_valid(mse_valid),
    .mse_in_value(mse_out),
    .mse_in_ref(mse_ref),  // Reference ID of the best match
    .clear(clear),  // Clear signal to reset MSE values
    .mse_min_value(mse_min_value),  // Not used in this module
    .mse_min_ref(mse_min_ref),  // Not used in this module
    .mse_min_changed(),  // Not used in this module
    .mse_max_value(mse_max_value),  // Not used in this module
    .mse_max_ref(mse_max_ref),  // Not used in this module
    .mse_max_changed(),  // Not used in this module
    .mse_out_valid(mse_comparison_valid)
  );

  fifo #(
    .DATA_WIDTH(WORD_WIDTH),
    .FIFO_DEPTH(ELEMENTS)  // FIFO depth for HSI bands
  ) fifo_measure (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(fifo_measure_write_en),
    .rd_en(fifo_both_read_en),
    .data_in(fifo_measure_data_in),
    .data_out(fifo_measure_data_out),
    .full(fifo_measure_full),
    .almost_full(),
    .empty(fifo_measure_empty)
  );

  fifo #(
    .DATA_WIDTH(WORD_WIDTH),
    .FIFO_DEPTH(BUFFER_LENGTH)  // Some buffer length for input vectors
  ) fifo_ref (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(fifo_ref_write_en),
    .rd_en(fifo_both_read_en),
    .data_in(hsi_vctr_in),
    .data_out(fifo_ref_data_out),
    .full(fifo_ref_full),
    .almost_full(),
    .empty(fifo_ref_empty)
  );

endmodule