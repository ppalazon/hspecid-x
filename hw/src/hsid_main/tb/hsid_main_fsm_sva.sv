`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_main_fsm_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Number of bits to represent vector length
  ) (
    input logic clk,
    input logic rst_n,

    input logic clear,

    // Library size input
    input logic [HSP_BANDS_WIDTH-1:0] hsp_bands,  // HSP bands to process
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_library_size,  // Length of the vectors

    // Configured parameters
    input logic [HSP_BANDS_WIDTH-1:0] cfg_band_pack_threshold,  // HSP bands packs to process
    input logic [HSP_BANDS_WIDTH-1:0] cfg_hsp_bands,  // HSP bands packs to process

    // Fifo status signals
    input logic fifo_captured_complete,  // Full signal for measure vector FIFO
    input logic fifo_captured_empty,  // Empty signal for measure vector FIFO
    input logic fifo_ref_empty,  // Empty signal for output data FIFO
    input logic fifo_ref_full,  // Full signal for output data FIFO

    // MSE signals
    input logic mse_valid,
    input logic mse_comparison_valid,

    // Current state
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_count,
    input logic band_pack_start,  // Start vector processing signal
    input logic band_pack_last,  // Last vector processing signal
    input logic band_pack_valid,  // Element valid signal
    input logic fifo_both_read_en,
    input logic initialize,

    // Block interface for handshake signals
    input logic start,
    input logic done,
    input logic idle,
    input logic ready,
    input logic error,
    input logic cancelled,

    // Internal signals for verification
    input hsid_main_state_t current_state, next_state,
    input logic [HSP_LIBRARY_WIDTH-1:0] cfg_hsp_library_size,
    input logic [HSP_BANDS_WIDTH-1:0] ref_band_pack_count,
    // input logic finished_library,
    input logic hsp_ref_last
  );

  localparam K = WORD_WIDTH;
  localparam DK = 2*K;
  localparam DIVIDER_LATENCY = K + 1; // Latency of the divider module

  // Increment of hsp_ref_count after band_pack_last
  property inc_hsp_ref_count;
    @(posedge clk) disable iff (!rst_n) band_pack_last |-> ##1 (hsp_ref_count == $past(hsp_ref_count) + 1);
  endproperty
  assert property (inc_hsp_ref_count) else $error("HSP reference count is not incremented correctly");
  cover property (inc_hsp_ref_count); // $display("Checked: HSP reference count is incremented correctly");

  // Restart hsp_ref_count on start signal
  property re_initilize;
    @(posedge clk) disable iff (!rst_n) current_state == HM_DONE || current_state == HM_CLEAR || current_state == HM_ERROR |-> ##1 (hsp_ref_count == 0)
      && (ref_band_pack_count == 0) && !band_pack_start && !band_pack_valid // && !finished_library
      && (cfg_hsp_bands == {HSP_BANDS_WIDTH{1'b1}}) && (cfg_hsp_library_size == {HSP_LIBRARY_WIDTH{1'b1}})
      && (cfg_band_pack_threshold == {HSP_BANDS_WIDTH{1'b1}});
  endproperty
  assert property (re_initilize) else $error("HSP reference count is not reset on start signal");
  cover property (re_initilize); // $display("Checked: HSP reference count is reset on start signal");

  // Initilize is only high for one clock cycle after start
  property initialize_high_on_done;
    @(posedge clk) disable iff (!rst_n) current_state == HM_DONE || current_state == HM_ERROR |-> initialize ##1 !initialize;
  endproperty
  assert property (initialize_high_on_done) else $error("Initialize signal is not high for one clock cycle after start");
  cover property (initialize_high_on_done); // $display("Checked: Initialize signal is high for one clock cycle after start");

  // Set band_pack_start when band_pack_count is zero
  property band_pack_start_on_zero;
    @(posedge clk) disable iff (!rst_n || clear) band_pack_valid && ref_band_pack_count == 0 && cfg_hsp_library_size > 1 |-> band_pack_start;
  endproperty
  assert property (band_pack_start_on_zero) else $error("Band pack start signal is not high when band pack count is zero");
  cover property (band_pack_start_on_zero); // $display("Checked: Band pack start signal is high when band pack count is zero");

  // Set band_pack_last when band_pack_count is equal to band_pack_threshold - 1
  property band_pack_last_on_threshold;
    @(posedge clk) disable iff (!rst_n || clear) band_pack_valid && ref_band_pack_count == cfg_band_pack_threshold - 1 |-> band_pack_last;
  endproperty
  assert property (band_pack_last_on_threshold) else $error("Band pack last signal is not high when band pack count is equal to band pack threshold - 1");
  cover property (band_pack_last_on_threshold); // $display("Checked: Band pack last signal is high when band pack count is equal to band pack threshold - 1");

  // Set band_pack_valid next clock cycle after read from both FIFOs
  property band_pack_valid_after_fifo_read;
    @(posedge clk) disable iff (!rst_n || clear) fifo_both_read_en |-> ##1 band_pack_valid;
  endproperty
  assert property (band_pack_valid_after_fifo_read) else $error("Band pack valid signal is not high next clock cycle after read from both FIFOs");
  cover property (band_pack_valid_after_fifo_read); // $display("Checked: Band pack valid signal is high next clock cycle after read from both FIFOs");

  // Increment band_pack_count after band_pack_last
  property inc_band_pack_count;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HM_COMPUTE_MSE && band_pack_valid && !band_pack_last |->
      ##1 (ref_band_pack_count == $past(ref_band_pack_count) + 1);
  endproperty
  assert property (inc_band_pack_count) else $error("Band pack count is not incremented correctly");
  cover property (inc_band_pack_count); // $display("Checked: Band pack count is incremented correctly");

  // Reset band_pack_count after band_pack_last
  property reset_band_pack_count;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HM_COMPUTE_MSE && band_pack_valid && band_pack_last |->
      ##1 (ref_band_pack_count == 0);
  endproperty
  assert property (reset_band_pack_count) else $error("Band pack count is not reset after last band pack");
  cover property (reset_band_pack_count); // $display("Checked: Band pack count is reset after last band pack");

  // Don't change back_pack_count out of HM_COMPUTE_MSE state
  property band_pack_count_stable_or_zero_out_of_compute_mse;
    @(posedge clk) disable iff (!rst_n || clear) current_state != HM_COMPUTE_MSE |-> ##1 $stable(ref_band_pack_count) || ref_band_pack_count == 0;
  endproperty
  assert property (band_pack_count_stable_or_zero_out_of_compute_mse) else $error("Band pack count is not stable out of HM_COMPUTE_MSE state");
  cover property (band_pack_count_stable_or_zero_out_of_compute_mse); // $display("Checked: Band pack count is stable out of HM_COMPUTE_MSE state");

  // After start, move to MAIN_CONFIG state
  property start_to_config;
    @(posedge clk) disable iff (!rst_n || clear) $past(rst_n) && current_state == HM_IDLE && start |->
      ##1 (current_state == HM_CONFIG)
      ##1 (current_state == HM_READ_HSP_CAPTURED) || (current_state == HM_ERROR);
  endproperty
  assert property (start_to_config) else $error("After start, state should change to HM_CONFIG state and then to READ_HSP_CAPTURED or ERROR state");
  cover property (start_to_config); // $display("Checked: After start, state should change to MAIN_CONFIG state and then to READ_HSP_CAPTURED or ERROR state");

  // Assert configuration parameters are only set in MAIN_CONFIG state
  property config_params_set_in_config_state;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HM_READ_HSP_CAPTURED || current_state == HM_COMPUTE_MSE || current_state == HM_COMPARE_MSE || current_state == HM_WAIT_MSE |-> ##1
      $stable(cfg_hsp_bands) && $stable(cfg_hsp_library_size) && $stable(cfg_band_pack_threshold);
  endproperty

  assert property (config_params_set_in_config_state) else $error("Configuration parameters has been modified out of MAIN_CONFIG state");
  cover property (config_params_set_in_config_state); // $display("Checked: Configuration parameters has been modified out of MAIN_CONFIG state");

  // Assert configuration parameters are set correctly in MAIN_CONFIG state
  property config_params_set_correctly;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HM_CONFIG |-> ##1
      cfg_hsp_bands == $past(hsp_bands) &&
      cfg_hsp_library_size == $past(hsp_library_size) &&
      cfg_band_pack_threshold == ($past(hsp_bands) + 1) / 2;
  endproperty

  // If hsp_ref_last is high, hsp_ref_count should be the last one
  property hsp_ref_count_last_on_hsp_ref_last;
    @(posedge clk) disable iff (!rst_n || clear) hsp_ref_last |-> (hsp_ref_count == cfg_hsp_library_size - 1);
  endproperty

  assert property (hsp_ref_count_last_on_hsp_ref_last) else $error("HSP reference count is not the last one when hsp_ref_last is high");
  cover property (hsp_ref_count_last_on_hsp_ref_last); // $display("Checked: HSP reference count is the last one when hsp_ref_last is high");

  // On captured complete, state should change to COMPUTE_MSE
  property state_change_on_captured_complete;
    @(posedge clk) disable iff (!rst_n || clear) fifo_captured_complete |-> ##1 (current_state != HM_READ_HSP_CAPTURED);
  endproperty
  assert property (state_change_on_captured_complete) else $error("State is not COMPUTE_MSE after captured complete");
  cover property (state_change_on_captured_complete); // $display("Checked: State is COMPUTE_MSE after captured complete");

  // Full reference FIFO should never be reached
  property no_full_ref_fifo;
    @(posedge clk) disable iff (!rst_n || clear) current_state == HM_COMPUTE_MSE |-> ##1 !fifo_ref_full;
  endproperty
  assert property (no_full_ref_fifo) else $error("Reference FIFO is full during processing");
  cover property (no_full_ref_fifo); // $display("Checked: Reference FIFO is not full during processing");

  // Ready signal should be high when state is READ_HSP_CAPTURED or COMPUTE_MSE
  property ready_signal_high_in_read_or_compute;
    @(posedge clk) disable iff (!rst_n || clear) ready |-> (current_state == HM_READ_HSP_CAPTURED || current_state == HM_COMPUTE_MSE);
  endproperty
  assert property (ready_signal_high_in_read_or_compute) else $error("Ready signal is high when it's not expected");
  cover property (ready_signal_high_in_read_or_compute); // $display("Checked: Ready signal is high when it's not expected");

  // Done signal should be high when state is DONE
  property done_signal_high_in_done_state;
    @(posedge clk) disable iff (!rst_n || clear) done |-> current_state == HM_DONE ## 1 !done;
  endproperty
  assert property (done_signal_high_in_done_state) else $error("Done signal is high when it's not expected");
  cover property (done_signal_high_in_done_state); // $display("Checked: Done signal is high when expected");

  // Error signal should be high when state is ERROR
  property error_signal_high_in_error_state;
    @(posedge clk) disable iff (!rst_n || clear) error |-> current_state == HM_ERROR ## 1 !error;
  endproperty
  assert property (error_signal_high_in_error_state) else $error("Error signal is high when it's not expected");
  cover property (error_signal_high_in_error_state); // $display("Checked: Error signal is high when expected");

  // Idle signal should be high when state is MAIN_IDLE
  property idle_signal_high_in_idle_state;
    @(posedge clk) disable iff (!rst_n || clear) idle |-> current_state == HM_IDLE;
  endproperty
  assert property (idle_signal_high_in_idle_state) else $error("Idle signal is high when it's not expected");
  cover property (idle_signal_high_in_idle_state); // $display("Checked: Idle signal is high when expected");

  // On clear, always move to MAIN_CLEAR state
  property computation_to_main_clear;
    @(posedge clk) disable iff (!rst_n) clear && (current_state != HM_CLEAR && current_state != HM_DONE && current_state != HM_IDLE && current_state != HM_ERROR) |->
      ##1 (current_state == HM_CLEAR) ## 1 (current_state == HM_IDLE);
  endproperty
  assert property (computation_to_main_clear) else $error("State is not MAIN_CLEAR after clear");
  cover property (computation_to_main_clear); // $display("Checked: State is MAIN_CLEAR after clear");

  // On last band of last HSP, finished_library should be high and next state should be WAIT_MSE
  property finish_mse_after_last_lib_band;
    @(posedge clk) disable iff (!rst_n || clear) band_pack_last && hsp_ref_last |->
      ##1 current_state == HM_WAIT_MSE
      ##(4 + DIVIDER_LATENCY) mse_valid
      ##1 !mse_valid && mse_comparison_valid && current_state == HM_COMPARE_MSE
      ##1 !mse_valid && !mse_comparison_valid && current_state == HM_DONE;
  endproperty
  assert property (finish_mse_after_last_lib_band) else $error("Finished library is not high on last band of last HSP");
  cover property (finish_mse_after_last_lib_band); // $

  // Valid mse signal after last band of any HSP
  property mse_valid_after_last_band;
    @(posedge clk) disable iff (!rst_n || clear) band_pack_last |-> ##(5 + DIVIDER_LATENCY) mse_valid ##1 mse_comparison_valid;
  endproperty
  assert property (mse_valid_after_last_band) else $error("MSE valid signal is not high after last band of any HSP");
  cover property (mse_valid_after_last_band); // $display("Checked: MSE valid signal is high after last band of any HSP");

  // Clear on configuration
  property clear_on_config;
    @(posedge clk) disable iff (!rst_n) clear && current_state == HM_CONFIG |-> ##1 (current_state == HM_CLEAR);
  endproperty
  assert property (clear_on_config) else $error("State is not MAIN_CLEAR after clear on configuration");
  cover property (clear_on_config); // $display("Checked: State is MAIN_CLEAR after clear on configuration");

  // Clear on read HSP captured
  property clear_on_read_hsp_captured;
    @(posedge clk) disable iff (!rst_n) clear && current_state == HM_READ_HSP_CAPTURED |-> ##1 (current_state == HM_CLEAR);
  endproperty
  assert property (clear_on_read_hsp_captured) else $error("State is not MAIN_CLEAR after clear on read HSP captured");
  cover property (clear_on_read_hsp_captured); // $display("Checked: State is MAIN_CLEAR after clear on read HSP captured");

  // Clear on compute MSE
  property clear_on_compute_mse;
    @(posedge clk) disable iff (!rst_n) clear && current_state == HM_COMPUTE_MSE |-> ##1 (current_state == HM_CLEAR);
  endproperty
  assert property (clear_on_compute_mse) else $error("State is not MAIN_CLEAR after clear on compute MSE");
  cover property (clear_on_compute_mse); // $display("Checked: State is MAIN_CLEAR after clear on compute MSE");

  // Clear on wait MSE
  property clear_on_wait_mse;
    @(posedge clk) disable iff (!rst_n) clear && current_state == HM_WAIT_MSE |-> ##1 (current_state == HM_CLEAR);
  endproperty
  assert property (clear_on_wait_mse) else $error("State is not MAIN_CLEAR after clear on wait MSE");
  cover property (clear_on_wait_mse); // $display("Checked: State is MAIN_CLEAR after clear on wait MSE");

  // Cancelled signal should be high when clear is high
  property cancelled_signal_on_clear;
    @(posedge clk) disable iff (!rst_n) current_state == HM_CLEAR |-> cancelled ##1 !cancelled;
  endproperty

  assert property (cancelled_signal_on_clear) else $error("Cancelled signal is not high when it's on clear status and only for one clock cycle");
  cover property (cancelled_signal_on_clear); // $display("Checked: Cancelled signal is not high when it's on clear status and only for one clock cycle");

endmodule
