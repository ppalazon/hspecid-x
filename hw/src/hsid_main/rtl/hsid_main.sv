`timescale 1ns / 1ps

import hsid_pkg::*;  // Import the package for HSI MSE

module hsid_main #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = DATA_WIDTH * 2,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = DATA_WIDTH * 3,  // Data width for accumulator, larger than WORD
    parameter HSI_BANDS = 255,  // Number of HSI bands
    parameter BUFFER_LENGTH = 4,  // Number of entries in the FIFO buffer
    parameter ELEMENTS = HSI_BANDS / 2, // Number of elements in the vector
    parameter HSI_LIBRARY_SIZE = 4095,  // Size of the HSI library
    parameter HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    localparam ELEMENTS_ADDR = $clog2(ELEMENTS),  // Address width for elements
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)  // Address width for HSI bands
  ) (
    input logic clk,
    input logic rst_n,

    // Input vector data
    input logic hsi_vctr_in_valid,  // Enable input sample data
    input logic [WORD_WIDTH-1:0] hsi_vctr_in, // Input sample word data

    // Input parameters for library size and pixel bands
    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] library_size_in,  // Amount of HSI library vectors to process
    input logic [HSI_BANDS_ADDR-1:0] hsi_bands_in,  // HSI bands to process

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

  wire hsid_main_state_t state;
  wire fifo_measure_complete, fifo_measure_empty;
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
  wire [ELEMENTS_ADDR-1:0] element_threshold; // Threshold for element count to restart the element count and check almost full condition
  assign element_threshold = (hsi_bands_in / 2);

  // Assigns statements
  assign fifo_measure_data_in = (state == READ_MEASURE) ? hsi_vctr_in : '0; //(state == COMPUTE_MSE ? fifo_measure_data_out : '0);
  assign fifo_measure_write_en = (state == READ_MEASURE && hsi_vctr_in_valid); // || (state == COMPUTE_MSE && fifo_measure_loop);
  assign fifo_ref_write_en = (state == COMPUTE_MSE && hsi_vctr_in_valid);

  hsid_main_fsm #(
    .HSI_BANDS(HSI_BANDS),
    .ELEMENTS(ELEMENTS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) fsm (
    .clk(clk),
    .rst_n(rst_n),
    .hsi_library_size(library_size_in),
    .fifo_measure_loop(),
    .fifo_measure_complete(fifo_measure_complete),
    .fifo_measure_empty(fifo_measure_empty),
    .fifo_ref_empty(fifo_ref_empty),
    .fifo_ref_full(fifo_ref_full),
    .msi_valid(mse_valid),  // MSE valid signal
    .msi_comparison_valid(mse_comparison_valid),  // MSE comparison valid signal
    .state(state),
    .vctr_count(vctr_ref),  // Not used in this module
    .element_threshold(element_threshold),
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

  hsid_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .HSI_BANDS(HSI_BANDS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL)
  ) hsi_mse (
    .clk(clk),
    .rst_n(rst_n),
    .element_start(element_start),
    .element_last(element_last),
    .vctr_ref(vctr_ref),
    .element_a(fifo_measure_data_out),
    .element_b(fifo_ref_data_out),
    .element_valid(element_valid),
    .hsi_bands(hsi_bands_in),
    .mse_value(mse_out),
    .mse_ref(mse_ref),
    .mse_valid(mse_valid)
  );

  hsid_mse_comp #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) hsi_mse_comp (
    .clk(clk),
    .rst_n(rst_n),
    .mse_in_valid(mse_valid),
    .mse_in_value(mse_out),
    .mse_in_ref(mse_ref),
    .clear(clear),
    .mse_min_value(mse_min_value),
    .mse_min_ref(mse_min_ref),
    .mse_min_changed(),
    .mse_max_value(mse_max_value),
    .mse_max_ref(mse_max_ref),
    .mse_max_changed(),
    .mse_out_valid(mse_comparison_valid)
  );

  hsid_fifo #(
    .DATA_WIDTH(WORD_WIDTH),
    .FIFO_DEPTH(ELEMENTS)  // FIFO depth for HSI bands
  ) fifo_measure (
    .clk(clk),
    .rst_n(rst_n),
    .loop_en(fifo_both_read_en),
    .wr_en(fifo_measure_write_en),
    .rd_en(fifo_both_read_en),
    .data_in(fifo_measure_data_in),
    .almost_full_threshold(element_threshold),  // Threshold for almost full condition
    .data_out(fifo_measure_data_out),
    .full(),
    .almost_full(fifo_measure_complete),
    .empty(fifo_measure_empty),
    .clear(clear)
  );

  hsid_fifo #(
    .DATA_WIDTH(WORD_WIDTH),
    .FIFO_DEPTH(BUFFER_LENGTH)  // Some buffer length for input vectors
  ) fifo_ref (
    .clk(clk),
    .rst_n(rst_n),
    .loop_en('0),  // No loop enable for this FIFO
    .wr_en(fifo_ref_write_en),
    .rd_en(fifo_both_read_en),
    .data_in(hsi_vctr_in),
    .almost_full_threshold(BUFFER_LENGTH - 1),  // Threshold for almost full condition
    .data_out(fifo_ref_data_out),
    .full(fifo_ref_full),
    .almost_full(),
    .empty(fifo_ref_empty),
    .clear(clear)
  );

endmodule