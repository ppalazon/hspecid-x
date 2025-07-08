`timescale 1ns / 1ps

module hsid_x_ctrl_reg #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    REG_BUS.in  regbus_slave,

    // HSpecID-X register for block interface for handshake
    output logic start,
    output logic clear,
    input logic idle,
    input logic ready,
    input logic done,
    input logic error,

    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] library_size,  // Size of the Hyperspectral pixel library
    output logic [HSI_BANDS_ADDR-1:0] pixel_bands,  // Number of bands per hyperspectral pixel

    output logic [WORD_WIDTH-1:0] captured_pixel_addr,  // Address of the captured pixel
    output logic [WORD_WIDTH-1:0] library_pixel_addr,  // Address of the library pixel

    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref, // Pixel reference for minimum MSE value
    input logic [WORD_WIDTH-1:0] mse_min_value,  // Minimum MSE value
    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref,  // Pixel reference for maximum MSE value
    input logic [WORD_WIDTH-1:0] mse_max_value  // Maximum MSE value
  );

  // Hardware <-> Register interface
  hsid_x_ctrl_reg_pkg::hsid_x_ctrl_reg2hw_t reg2hw;
  hsid_x_ctrl_reg_pkg::hsid_x_ctrl_hw2reg_t hw2reg;

  // Block writing when HSpecID-X is activate
  // assign regbus_slave.write = regbus_slave.write && idle;

  //

  hsid_x_ctrl_reg_top_intf hsid_x_ctrl_reg_top_inst (
    .clk_i(clk),
    .rst_ni(rst_n),

    // Register interface (Request and response)
    .regbus_slave(regbus_slave),

    // Register to HW interface
    .reg2hw(reg2hw),

    // HW to register interface
    .hw2reg(hw2reg),

    .devmode_i(1'b0)  // Device mode, not used in this module
  );

  // Register to HW interface (Output)
  assign start = reg2hw.status.start.q;
  assign clear = reg2hw.status.clear.q;
  assign captured_pixel_addr = reg2hw.captured_pixel_addr.q;
  assign library_pixel_addr = reg2hw.library_pixel_addr.q;
  assign library_size = reg2hw.library_size.q[HSI_LIBRARY_SIZE_ADDR-1:0];
  assign pixel_bands = reg2hw.pixel_bands.q[HSI_BANDS_ADDR-1:0];  // Number of bands

  // HW to Register interface (Input)
  assign hw2reg.status.idle.d = idle;
  assign hw2reg.status.idle.de = 1'b1;
  assign hw2reg.status.done.d = done;
  assign hw2reg.status.done.de = 1'b1;
  assign hw2reg.status.error.d = error;
  assign hw2reg.status.error.de = 1'b1;
  assign hw2reg.status.ready.d = ready;
  assign hw2reg.status.ready.de = 1'b1;

  assign hw2reg.mse_min_ref.d = {{(WORD_WIDTH-HSI_LIBRARY_SIZE_ADDR){1'b0}}, mse_min_ref}; // Zero-extend to match width
  assign hw2reg.mse_min_ref.de = 1'b1;

  assign hw2reg.mse_min_value.d = mse_min_value;
  assign hw2reg.mse_min_value.de = 1'b1;

  assign hw2reg.mse_max_ref.d = {{(WORD_WIDTH-HSI_LIBRARY_SIZE_ADDR){1'b0}}, mse_max_ref}; // Zero-extend to match width
  assign hw2reg.mse_max_ref.de = 1'b1;

  assign hw2reg.mse_max_value.d = mse_max_value;
  assign hw2reg.mse_max_value.de = 1'b1;

  // Software set start bit, and this bit is always cleared by hardware. It's only high for one clock cycle
  assign hw2reg.status.start.d  = 1'b0;
  assign hw2reg.status.start.de = 1'b1;

  // Software set clear bit, and this bit is always cleared by hardware. It's only high for one clock cycle
  assign hw2reg.status.clear.d  = 1'b0;
  assign hw2reg.status.clear.de = 1'b1;


endmodule

