`timescale 1ns/1ps

import hsid_pkg::*;

module hsid_divider_sva #(
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter K = 32, // Number of bits for quotient and remainder
    localparam DK = 2*K // Number of bits for dividend
  ) (
    input logic clk,
    input logic rst_n,
    input logic clear,
    input logic start,
    input logic [DK-1:0] dividend,
    input logic [K-1:0] divisor,
    input logic of_in, // Dividend or divisor is overflowed
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_in,

    // Outputs
    input logic idle,
    input logic done,
    input logic ready,
    input logic [K-1:0] quotient,
    input logic [K-1:0] remainder,
    input logic overflow,
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_out,

    // Internal signals
    input hsid_ite_div_state_t state,
    input hsid_ite_div_state_t next_state
  );

  property clear_to_idle;
    @(posedge clk) disable iff (!rst_n)
      clear && state != HID_IDLE |-> ##1 state == HID_CLEAR ##1 idle;
  endproperty

  assert property (clear_to_idle) else $error("SVA Failed: clear_to_idle");
  cover property (clear_to_idle);

  property start_to_done_no_overflow;
    @(posedge clk) disable iff (!rst_n || clear)
      start && state == HID_IDLE ##1 !overflow |-> state == HID_COMPUTE ##(K) state == HID_CHECK ##1 done;
  endproperty

  assert property (start_to_done_no_overflow) else $error("SVA Failed: start_to_done_no_overflow");
  cover property (start_to_done_no_overflow);

  property divided_by_zero;
    @(posedge clk) disable iff (!rst_n || clear)
      start && divisor == 0 |-> ##1 overflow ##1 done ##1 idle;
  endproperty

  assert property (divided_by_zero) else $error("SVA Failed: divided_by_zero");
  // cover property (divided_by_zero);

  property dividend_divisor_overflow;
    @(posedge clk) disable iff (!rst_n || clear)
      start && (dividend >= {{K{1'b0}}, divisor} << K) |-> ##1 overflow ##1 done ##1 idle;
  endproperty

  assert property (dividend_divisor_overflow) else $error("SVA Failed: dividend_divisor_overflow");

  property start_with_overflow;
    @(posedge clk) disable iff (!rst_n || clear)
      start && of_in |-> ##1 overflow ##1 done ##1 idle;
  endproperty

  assert property (start_with_overflow) else $error("SVA Failed: start_with_overflow");

endmodule