`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_obi_mem_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter MEM_ACCESS_WIDTH = HSID_MEM_ACCESS_WIDTH  // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    // Obi interface
    // OBI_BUS.Manager obi_manager,
    input wire hsid_x_obi_inf_pkg::obi_req_t obi_req,
    input wire hsid_x_obi_inf_pkg::obi_resp_t obi_rsp,

    input logic [WORD_WIDTH-1:0] initial_addr,
    input logic [MEM_ACCESS_WIDTH-1:0] limit,

    input logic data_out_valid,
    input logic [WORD_WIDTH-1:0] data_out,

    input logic start,
    input logic clear,
    input logic idle,
    input logic ready,
    input logic done,

    // Internal signals
    input hsid_x_obi_mem_state_t current_state = HXOM_IDLE, next_state = HXOM_INIT,
    input logic [MEM_ACCESS_WIDTH-1:0] current_limit,
    input logic [MEM_ACCESS_WIDTH:0] requests,
    input logic [MEM_ACCESS_WIDTH:0] reads,
    input logic finish_requesting,
    input logic finish_reading
  );

  // If we try to start and clear at the same time during IDLE state, it shouldn't start
  property p_start_clear_idle;
    @(posedge clk) disable iff (!rst_n) current_state == HXOM_IDLE && start && clear |->
      ##1 current_state == HXOM_IDLE;
  endproperty
  assert property (p_start_clear_idle) else $error("Start and Clear cannot be asserted simultaneously in IDLE state");
  cover property (p_start_clear_idle); //$display("Coverage: Start and Clear in IDLE state");

  // After starting, the state should change to INIT and then to READING
  property p_start_to_init_to_reading;
    @(posedge clk) disable iff (!rst_n || clear) start && !clear && current_state == HXOM_IDLE |->
      ##1 (current_state == HXOM_INIT) ##1 (current_state == HXOM_READING);
  endproperty
  assert property (p_start_to_init_to_reading) else $error("After starting, the state should change from IDLE to INIT and then to READING");
  cover property (p_start_to_init_to_reading); //$display("Coverage: Start to INIT to READING");

  // During READING state, OBI request must be high until the limit is reached
  property p_reading_obi_req;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HXOM_READING && requests < current_limit |-> ##1
      obi_req.req;
  endproperty
  assert property (p_reading_obi_req) else $error("During READING state, OBI request must be high until the limit is reached");
  cover property (p_reading_obi_req); //$display("Coverage: READING state OBI request");

  // When requests reaches the limit, we must wait for the reading the last request and then DONE state
  property p_limit_reached_to_done;
    @(posedge clk) disable iff (!rst_n || clear) $rose(finish_requesting) && current_state == HXOM_READING |-> ##1
      !obi_req.req && finish_reading ##1 (current_state == HXOM_DONE);
  endproperty
  assert property (p_limit_reached_to_done) else $error("When requests reaches the limit, we must wait for the reading the last request and then DONE state");
  cover property (p_limit_reached_to_done); //$display("Coverage: Limit reached to DONE state");

  // On clear, the state should return to IDLE and all signals should be reset
  property p_clear_to_idle;
    @(posedge clk) disable iff (!rst_n) clear && (current_state == HXOM_INIT || current_state == HXOM_READING) |->
      ##1 current_state == HXOM_CLEAR && done == 1'b0 && ready == 1'b0 && idle == 1'b0
      ##1 current_state == HXOM_IDLE && !obi_req.req && current_limit == '0 &&
      !data_out_valid && data_out == '0 && requests == '0 && reads == '0;
  endproperty
  assert property (p_clear_to_idle) else $error("On clear, the state should return to IDLE and all signals should be reset, %0h", limit);
  cover property (p_clear_to_idle); //$display("Coverage: Clear to IDLE state");

  // If limit is 0 during INIT state, it should be set to maximum value to avoid infinite loop
  property p_limit_zero_to_max;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HXOM_INIT && limit == '0 |-> ##1 current_limit == '1;
  endproperty
  assert property (p_limit_zero_to_max) else $error("If limit is 0 during INIT state, it should be set to maximum value to avoid infinite loop");
  cover property (p_limit_zero_to_max); //$display("Coverage: Limit zero to maximum value");

  // After granted OBI response, the counter should increment
  property p_prepare_next_request;
    @(posedge clk) disable iff (!rst_n || clear) obi_req.req && obi_rsp.gnt && current_state == HXOM_READING |-> ##1
      requests == $past(requests) + 1 && obi_req.addr == $past(obi_req.addr) + 4;
  endproperty
  assert property (p_prepare_next_request) else $error("After granted OBI response, the counter should increment");
  cover property (p_prepare_next_request); //$display("Coverage: Granted increment");

  // After rvalid OBI response, relay the data out immediately
  property p_data_out_valid;
    @(posedge clk) disable iff (!rst_n || clear || finish_reading) obi_rsp.rvalid && current_state == HXOM_READING |->
      ##1 data_out_valid && data_out == $past(obi_rsp.rdata) && reads == $past(reads) + 1;
  endproperty
  assert property (p_data_out_valid) else $error("After rvalid OBI response, relay the data out immediately");
  cover property (p_data_out_valid); //$display("Coverage: Data out valid");

endmodule