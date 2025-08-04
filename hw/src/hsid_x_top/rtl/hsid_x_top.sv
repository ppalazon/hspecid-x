`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_top #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator
    parameter BUFFER_WIDTH = HSID_FIFO_ADDR_WIDTH,  // Number of entries in the FIFO buffer
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    input hsid_x_reg_pkg::reg_req_t reg_req_i,
    output hsid_x_reg_pkg::reg_rsp_t reg_rsp_o,

    // OBI interface (Master)
    input hsid_x_obi_inf_pkg::obi_resp_t obi_rsp_i,
    output hsid_x_obi_inf_pkg::obi_req_t obi_req_o,

    // Interrupt interface
    output logic hsid_x_int_o
  );

  wire start;
  wire clear;
  wire idle;
  wire ready;
  wire done;
  wire error;

  wire [HSP_LIBRARY_WIDTH-1:0] library_size;
  wire [HSP_BANDS_WIDTH-1:0] pixel_bands;
  wire [WORD_WIDTH-1:0] captured_pixel_addr;
  wire [WORD_WIDTH-1:0] library_pixel_addr;

  wire [HSP_LIBRARY_WIDTH-1:0] mse_min_ref; // Pixel reference for minimum MSE value
  wire [WORD_WIDTH-1:0] mse_min_value;  // Minimum MSE
  wire [HSP_LIBRARY_WIDTH-1:0] mse_max_ref;  // Pixel reference for maximum MSE value
  wire [WORD_WIDTH-1:0] mse_max_value;  // Maximum MSE

  wire obi_data_out_valid;
  wire [WORD_WIDTH-1:0] obi_data_out;
  wire [WORD_WIDTH-1:0] obi_initial_addr;
  wire [HSP_LIBRARY_WIDTH-1:0] obi_limit_in;
  wire obi_start;
  wire obi_done;

  assign hsid_x_int_o = done;

  hsid_x_top_fsm #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) fsm (
    .clk(clk),
    .rst_n(rst_n),
    .pixel_bands(pixel_bands),
    .library_size(library_size),
    .captured_pixel_addr(captured_pixel_addr),
    .library_pixel_addr(library_pixel_addr),
    .start(start),
    .clear(clear),
    .obi_initial_addr(obi_initial_addr),
    .obi_limit_in(obi_limit_in),
    .obi_start(obi_start),
    .obi_done(obi_done),
    .error(error)
  );


  // Register interface to hardware interface
  hsid_x_ctrl_reg #(
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .WORD_WIDTH(WORD_WIDTH)
  ) hsid_x_ctrl_reg (
    .clk(clk),
    .rst_n(rst_n),
    .reg_req(reg_req_i),
    .reg_rsp(reg_rsp_o),
    .start(start),
    .clear(clear),
    .idle(idle),
    .ready(ready),
    .done(done),
    .error(error),
    .library_size(library_size),
    .pixel_bands(pixel_bands),
    .captured_pixel_addr(captured_pixel_addr),
    .library_pixel_addr(library_pixel_addr),
    .mse_min_ref(mse_min_ref),
    .mse_min_value(mse_min_value),
    .mse_max_ref(mse_max_ref),
    .mse_max_value(mse_max_value)
  );

  // OBI interface to memory interface
  hsid_x_obi_mem #(
    .WORD_WIDTH      (WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  )
  u_hsid_x_obi_mem (
    .clk           (clk),
    .data_out      (obi_data_out),
    .data_out_valid(obi_data_out_valid),
    .done          (obi_done),
    .idle          (),
    .initial_addr  (obi_initial_addr),
    .limit         (obi_limit_in),
    .obi_req       (obi_req_o),
    .obi_rsp       (obi_rsp_i),
    .ready         (),
    .rst_n         (rst_n),
    .start         (obi_start)
  );

  // HSID Main module instantiation
  hsid_main #(
    .WORD_WIDTH (WORD_WIDTH),
    .DATA_WIDTH (DATA_WIDTH),
    .DATA_WIDTH_MUL (DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC (DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH (HSP_BANDS_WIDTH),
    .BUFFER_WIDTH (BUFFER_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  )
  u_hsid_main (
    // Clear signal to reset MSE values
    .clear            (clear),
    .clk              (clk),
    .done             (done),
    .hsp_bands_in     (pixel_bands),
    .band_data_in      (obi_data_out),
    .band_data_in_valid(obi_data_out_valid),
    .idle             (idle),
    .hsp_library_size_in  (library_size),
    .mse_max_ref      (mse_max_ref),
    .mse_max_value    (mse_max_value),
    .mse_min_ref      (mse_min_ref),
    .mse_min_value    (mse_min_value),
    .ready            (ready),
    .rst_n            (rst_n),
    .start            (start)
  );



endmodule