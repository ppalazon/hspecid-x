`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_top_fsm_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter MEM_ACCESS_WIDTH = HSID_MEM_ACCESS_WIDTH
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    input [HSP_BANDS_WIDTH-1:0] hsp_bands,  // HSP bands to process
    input [HSP_LIBRARY_WIDTH-1:0] hsp_library_size,  // Size of the HSI library
    input [WORD_WIDTH-1:0] captured_pixel_addr,  // Address for captured pixel data
    input [WORD_WIDTH-1:0] library_pixel_addr,  // Address for library pixel data
    input logic start,  // Start signal to initiate the FSM
    input logic clear,  // Clear signal to reset MSE values
    input logic error,  // Error flag
    input logic done,  // Idle signal indicating FSM is not processing
    input logic cancelled,  // Cancel signal to stop reading from OBI
    input logic interrupt,  // Idle signal indicating FSM is not processing

    // OBI interface signals
    input logic [WORD_WIDTH-1:0] obi_initial_addr,
    input logic [MEM_ACCESS_WIDTH-1:0] obi_limit_in,
    input logic obi_start,
    input wire obi_done,

    // Internal signals
    input hsid_x_top_t current_state = HXT_IDLE, next_state = HXT_START_READ_CAPTURED,
    input logic [WORD_WIDTH-1:0] cfg_captured_pixel_addr,
    input logic [WORD_WIDTH-1:0] cfg_library_pixel_addr,
    input logic [HSP_LIBRARY_WIDTH-1:0] cfg_hsp_library_size,
    input logic [HSP_BANDS_WIDTH-1:0] cfg_band_pack_threshold
  );

  // On start, the FSM should transition to CONFIG state, then to START_READ_CAPTURED and finally to HXT_READ_CAPTURED or HXT_CLEAR
  property p_start_to_reading;
    @(posedge clk) disable iff (!rst_n || clear) start && !clear && current_state == HXT_IDLE |->
      ##1 (current_state == HXT_CONFIG) ##1 (current_state == HXT_START_READ_CAPTURED) ##1 current_state == HXT_CLEAR || current_state == HXT_READ_CAPTURED;
  endproperty
  assert property (p_start_to_reading) else $error("FSM should transition from IDLE to CONFIG, then to START_READ_CAPTURED and finally to HXT_READ_CAPTURED or HXT_CLEAR on start");
  cover property (p_start_to_reading); //$display("Coverage: FSM transition on start");

  // Obi start signal must be high for only one clock cycle
  property p_obi_start_one_cycle;
    @(posedge clk) disable iff (!rst_n) obi_start |-> ##1 !obi_start;
  endproperty
  assert property (p_obi_start_one_cycle) else $error("OBI start signal should only be high for one clock cycle");
  cover property (p_obi_start_one_cycle); //$display("Coverage: OBI start signal one cycle");

  // Obi done signal must be high for only one clock cycle
  property p_obi_done_one_cycle;
    @(posedge clk) disable iff (!rst_n) obi_done |-> ##1 !obi_done;
  endproperty
  assert property (p_obi_done_one_cycle) else $error("OBI done signal should only be high for one clock cycle");
  cover property (p_obi_done_one_cycle); //$display("Coverage: OBI done signal one cycle");

  // Configured options must only be changed during CONFIG state
  property p_cfg_change_during_config;
    @(posedge clk) disable iff (!rst_n) current_state == HXT_CONFIG |-> ##1
      cfg_captured_pixel_addr == $past(captured_pixel_addr) &&
      cfg_library_pixel_addr == $past(library_pixel_addr) &&
      cfg_hsp_library_size == $past(hsp_library_size) &&
      cfg_band_pack_threshold == ($past(hsp_bands) + 1) / 2;
  endproperty
  assert property (p_cfg_change_during_config) else $error("Configured options should only change during CONFIG state");
  cover property (p_cfg_change_during_config); //$display("Coverage: Config options change during CONFIG state");

  // Configured options must not change during other states
  property p_cfg_no_change_other_states;
    @(posedge clk) disable iff (!rst_n) current_state != HXT_CONFIG && current_state != HXT_CLEAR |-> ##1
      $stable(cfg_band_pack_threshold) && $stable(cfg_captured_pixel_addr)  &&
      $stable(cfg_library_pixel_addr) && $stable(cfg_hsp_library_size);
  endproperty
  assert property (p_cfg_no_change_other_states) else $error("Configured options should not change during other states");
  cover property (p_cfg_no_change_other_states); //$display("Coverage: Config options do not change during other states");

  // Interrupt signal must be high when done, error, or cancelled
  property p_interrupt_signal;
    @(posedge clk) disable iff (!rst_n) (done || error || cancelled) |-> interrupt ##1 !interrupt;
  endproperty
  assert property (p_interrupt_signal) else $error("Interrupt signal should be high when done, error, or cancelled");
  cover property (p_interrupt_signal); //$display("Coverage: Interrupt signal high when done, error, or cancelled");



endmodule