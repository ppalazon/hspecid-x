`timescale 1ns / 1ps

module hsid_x_top #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = 32,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = 48,  // Data width for accumulator, larger than WORD
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    input hsid_x_ri_pkg::reg_req_t reg_req_i,
    output hsid_x_ri_pkg::reg_rsp_t reg_rsp_o,

    // OBI interface (Master)
    input hsid_x_obi_inf_pkg::obi_resp_t obi_rsp_i,
    output hsid_x_obi_inf_pkg::obi_req_t obi_req_o,

    // Interrupt interface
    output logic hsid_x_int_o
  );



endmodule