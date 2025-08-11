`timescale 1ns / 1ns

import hsid_pkg::*;

module hsid_x_registers_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    // REG_BUS.in  regbus_slave,
    input wire hsid_x_reg_pkg::reg_req_t reg_req,  // Register interface request
    input wire hsid_x_reg_pkg::reg_rsp_t reg_rsp,  // Register interface response

    // HSpecID-X register for block interface for handshake
    input logic start,
    input logic clear,
    input logic idle,
    input logic ready,
    input logic done,
    input logic error,
    input logic cancelled,

    input logic interruption,

    input logic [HSP_LIBRARY_WIDTH-1:0] library_size,  // Size of the Hyperspectral pixel library
    input logic [HSP_BANDS_WIDTH-1:0] pixel_bands,  // Number of bands per hyperspectral pixel

    input logic [WORD_WIDTH-1:0] captured_pixel_addr,  // Address of the captured pixel
    input logic [WORD_WIDTH-1:0] library_pixel_addr,  // Address of the library pixel

    input logic [HSP_LIBRARY_WIDTH-1:0] mse_min_ref, // Pixel reference for minimum MSE value
    input logic [WORD_WIDTH-1:0] mse_min_value,  // Minimum MSE value
    input logic [HSP_LIBRARY_WIDTH-1:0] mse_max_ref,  // Pixel reference for maximum MSE value
    input logic [WORD_WIDTH-1:0] mse_max_value,  // Maximum MSE value

    // Internal signals
    input hsid_x_ctrl_reg_pkg::hsid_x_ctrl_reg2hw_t reg2hw,
    input hsid_x_ctrl_reg_pkg::hsid_x_ctrl_hw2reg_t hw2reg
  );

  // Check that mse_min_ref and mse_max_ref are only changed after an interruption (done, cancelled, or error)
  property p_mse_output_change_after_interruption;
    @(posedge clk) disable iff (!rst_n) interruption |-> ##1
      hw2reg.mse_min_ref.d == mse_min_ref && hw2reg.mse_max_ref.d == mse_max_ref &&
      hw2reg.mse_min_value.d == mse_min_value && hw2reg.mse_max_value.d == mse_max_value;
  endproperty
  assert property (p_mse_output_change_after_interruption) else $error("MSE references should only change after an interruption");
  cover property (p_mse_output_change_after_interruption); //$display("Coverage: MSE references change after interruption");

  // Check that start signal will only be high during a clock cycle
  property p_start_signal_one_cycle;
    @(posedge clk) disable iff (!rst_n) start |-> ##1 !start;
  endproperty
  assert property (p_start_signal_one_cycle) else $error("Start signal should only be high for one clock cycle");
  cover property (p_start_signal_one_cycle); //$display("Coverage: Start signal one cycle");

  // Check that clear signal will only be high during a clock cycle
  property p_clear_signal_one_cycle;
    @(posedge clk) disable iff (!rst_n) clear |-> ##1 !clear;
  endproperty
  assert property (p_clear_signal_one_cycle) else $error("Clear signal should only be high for one clock cycle");
  cover property (p_clear_signal_one_cycle); //$display("Coverage: Clear signal one cycle");

endmodule