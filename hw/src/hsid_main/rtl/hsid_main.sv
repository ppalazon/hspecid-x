`timescale 1ns / 1ps

import hsid_pkg::*;  // Import the package for HSI MSE

/*
 @WAVEDROM_START
 { "signal": [
 { "name": "clk",                 "wave": "p..............|..|..............." },
 { "name": "band_data_in_valid",  "wave": "l..h...........|..|.l............." },
 {                                  node: '...A.........BC..D..E.............'},
 { "name": "band_data_in",        "wave": "x..3333333333x7|79|9x.............", "data": ["0/1","2/3","4/5","6/7","8/9","9/8","7/6","5/4","3/2","1/0","7/2","3/0","8/3","2/5"] },
 { "name": "hap_library_size_in", "wave": "x.5x...........|..|...............", "data":["2"] },
 { "name": "hap_bands_in",        "wave": "x.4x...........|..|..............." , "data":["20"] },
 { "name": "mse_min_ref",         "wave": "x..............|..|..6x.........6x" , "data":["0","0"] },
 { "name": "mse_max_ref",         "wave": "x..............|..|..8x.........8x" , "data":["0","1"] },
 { "name": "mse_min_value",       "wave": "x..............|..|..6x.........6x" , "data":["9","9"] },
 { "name": "mse_max_value",       "wave": "x..............|..|..8x.........8x" , "data":["9","21"] },
 {                                  node: '...................FGHIJKL.....MN.'},
 { "name": "start",               "wave": "lhl............|..|..............." },
 { "name": "done",                "wave": "l..............|..|.............hl" },
 { "name": "idle",                "wave": "hl.............|..|..............h" },
 { "name": "ready",               "wave": "l..h...........|..|l.............." }
 ],
 edge: [
 'A+B HSP', 'C+D Ref 0', 'D+E Ref 1',
 'F+G W/F', 'G+H R/F', 'H+I Diff', 'I+J Mult','J+K Acc','K+L Sum','L+M Divider', 'M+N Comp'
 ]
 }
 @WAVEDROM_END
 */
module hsid_main #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than WORD
    parameter BUFFER_WIDTH = HSID_FIFO_ADDR_WIDTH,  // Number of bits for buffer address (4 entries)
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Address width for HSP bands
  ) (
    input logic clk,
    input logic rst_n,

    // Clear signal to reset MSE values
    input logic clear,

    // Input vector data
    input logic band_data_in_valid,  // Enable input sample data
    input logic [WORD_WIDTH-1:0] band_data_in, // Input sample word data

    // Input parameters for library size and pixel bands
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_library_size_in,  // Amount of HSI library vectors to process
    input logic [HSP_BANDS_WIDTH-1:0] hsp_bands_in,  // HSP bands to process

    // Output parameters with the MSE result
    output logic [HSP_LIBRARY_WIDTH-1:0] mse_min_ref,
    output logic [HSP_LIBRARY_WIDTH-1:0] mse_max_ref,
    output logic [WORD_WIDTH-1:0] mse_min_value,  // Mean Squared Error output
    output logic [WORD_WIDTH-1:0] mse_max_value,  // Mean Squared Error output

    // Standard block interface handshake signals
    input logic start,
    output logic done,
    output logic idle,
    output logic ready,
    output logic error,
    output logic cancelled
  );

  // wire hsid_main_state_t state;
  wire fifo_captured_complete, fifo_captured_empty;
  wire fifo_ref_full, fifo_ref_empty;

  wire [WORD_WIDTH-1:0] fifo_captured_data_in;
  wire fifo_captured_write_en, fifo_ref_write_en;
  wire fifo_both_read_en;

  wire [WORD_WIDTH-1:0] fifo_captured_data_out, fifo_ref_data_out;

  wire mse_valid;  // MSE valid signal
  wire acc_of;  // Overflow flag for the accumulated vector
  wire mse_comparison_valid;  // MSE valid signal
  wire band_pack_start;  // Start vector processing signal
  wire band_pack_last;  // Last vector processing signal
  wire band_pack_valid; // Element valid signal
  wire [HSP_LIBRARY_WIDTH-1:0] hsp_ref;  // Reference vector for MSE
  wire [WORD_WIDTH-1:0] mse_out;  // Mean Squared Error
  wire [HSP_LIBRARY_WIDTH-1:0] mse_ref;  // Reference vector for MSE
  wire initialize;

  // Assigns statements
  wire [HSP_BANDS_WIDTH-1:0] cfg_band_pack_threshold;
  wire [HSP_BANDS_WIDTH-1:0] cfg_hsp_bands;

  hsid_main_fsm #(
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) fsm (
    .clk(clk),
    .rst_n(rst_n),
    .clear(clear),
    .band_data_in_valid(band_data_in_valid),
    .band_data_in(band_data_in),
    .hsp_bands(hsp_bands_in),
    .hsp_library_size(hsp_library_size_in),
    .fifo_captured_complete(fifo_captured_complete),
    .fifo_captured_empty(fifo_captured_empty),
    .fifo_ref_empty(fifo_ref_empty),
    .fifo_ref_full(fifo_ref_full),
    .fifo_captured_data_in(fifo_captured_data_in),
    .fifo_captured_write_en(fifo_captured_write_en),
    .fifo_ref_write_en(fifo_ref_write_en),
    .mse_valid(mse_valid),
    .mse_comparison_valid(mse_comparison_valid),
    .mse_ref(mse_ref),
    .cfg_band_pack_threshold(cfg_band_pack_threshold),
    .cfg_hsp_bands(cfg_hsp_bands),
    .hsp_ref_count(hsp_ref),
    .band_pack_start(band_pack_start),  // Start vector processing signal
    .band_pack_last(band_pack_last),
    .band_pack_valid(band_pack_valid),
    .fifo_both_read_en(fifo_both_read_en),  // FIFO read enable signal
    .initialize(initialize),  // Initialize signal to clear submodules
    .start(start),
    .done(done),
    .idle(idle),
    .ready(ready),
    .error(error),
    .cancelled(cancelled)
  );

  hsid_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL)
  ) mse (
    .clk(clk),
    .rst_n(rst_n),
    .clear(clear || initialize),
    .band_pack_start(band_pack_start),
    .band_pack_last(band_pack_last),
    .hsp_ref(hsp_ref),
    .band_pack_a(fifo_captured_data_out),
    .band_pack_b(fifo_ref_data_out),
    .band_pack_valid(band_pack_valid),
    .hsp_bands(cfg_hsp_bands),
    .mse_value(mse_out),
    .mse_ref(mse_ref),
    .mse_valid(mse_valid),
    .acc_of(acc_of)
  );

  hsid_mse_comp #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) mse_comp (
    .clk(clk),
    .rst_n(rst_n),
    .mse_in_valid(mse_valid),  // Valid MSE output and no overflow
    .mse_in_of(acc_of),
    .mse_in_value(mse_out),
    .mse_in_ref(mse_ref),
    .clear(clear || initialize),
    .mse_min_value(mse_min_value),
    .mse_min_ref(mse_min_ref),
    .mse_min_changed(),
    .mse_max_value(mse_max_value),
    .mse_max_ref(mse_max_ref),
    .mse_max_changed(),
    .mse_out_valid(mse_comparison_valid)
  );

  hsid_fifo #(
    .WORD_WIDTH(WORD_WIDTH),
    .FIFO_ADDR_WIDTH(HSP_BANDS_WIDTH)  // FIFO depth for HSP bands
  ) fifo_captured (
    .clk(clk),
    .rst_n(rst_n),
    .loop_en(fifo_both_read_en),
    .wr_en(fifo_captured_write_en),
    .rd_en(fifo_both_read_en),
    .data_in(fifo_captured_data_in),
    .almost_full_threshold(cfg_band_pack_threshold),  // Threshold for almost full condition
    .data_out(fifo_captured_data_out),
    .full(),
    .almost_full(fifo_captured_complete),
    .empty(fifo_captured_empty),
    .clear(clear || initialize)
  );

  hsid_fifo #(
    .WORD_WIDTH(WORD_WIDTH),
    .FIFO_ADDR_WIDTH(BUFFER_WIDTH)  // Some buffer length for input vectors
  ) fifo_ref (
    .clk(clk),
    .rst_n(rst_n),
    .loop_en('0),  // No loop enable for this FIFO
    .wr_en(fifo_ref_write_en),
    .rd_en(fifo_both_read_en),
    .data_in(band_data_in),
    .almost_full_threshold({BUFFER_WIDTH,{1'b1}}),  // Threshold for almost full condition
    .data_out(fifo_ref_data_out),
    .full(fifo_ref_full),
    .almost_full(),
    .empty(fifo_ref_empty),
    .clear(clear || initialize)
  );

endmodule