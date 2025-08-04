`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_main_fsm_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // Data width for HSP bands
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Number of bits to represent vector length
  ) (
    input logic clk,
    input logic rst_n,

    input logic clear,

    // Library size input
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_library_size,  // Length of the vectors
    input logic [HSP_BANDS_WIDTH-1:0] band_pack_threshold,  // HSP bands to process

    // Fifo status signals
    input logic fifo_captured_complete,  // Full signal for measure vector FIFO
    input logic fifo_captured_empty,  // Empty signal for measure vector FIFO
    input logic fifo_ref_empty,  // Empty signal for output data FIFO
    input logic fifo_ref_full,  // Full signal for output data FIFO

    // MSE signals
    input logic mse_valid,
    input logic mse_comparison_valid,

    // Current state
    input hsid_main_state_t state,
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_count,
    input logic band_pack_start,  // Start vector processing signal
    input logic band_pack_last,  // Last vector processing signal
    input logic band_pack_valid,  // Element valid signal
    input logic hsp_ref_last,
    input logic finished_library,
    input logic fifo_both_read_en,
    input logic initialize,

    // Block interface for handshake signals
    input logic start,
    input logic done,
    input logic idle,
    input logic ready,

    // Internal signals for verification
    input logic [HSP_BANDS_WIDTH:0] band_pack_count
  );

  // Increment of hsp_ref_count after band_pack_last
  property inc_hsp_ref_count;
    @(posedge clk) disable iff (!rst_n) band_pack_last |-> ##1 (hsp_ref_count == $past(hsp_ref_count) + 1);
  endproperty
  assert property (inc_hsp_ref_count) else $error("HSP reference count is not incremented correctly");
  cover property (inc_hsp_ref_count); // $display("Checked: HSP reference count is incremented correctly");

  // Restart hsp_ref_count on start signal
  property re_initilize;
    @(posedge clk) disable iff (!rst_n) state == DONE |-> ##1 (hsp_ref_count == 0)
      && (band_pack_count == 0) && !band_pack_start && !band_pack_valid && !finished_library;
  endproperty
  assert property (re_initilize) else $error("HSP reference count is not reset on start signal");
  cover property (re_initilize); // $display("Checked: HSP reference count is reset on start signal");

  // Initilize is only high for one clock cycle after start
  property initialize_high;
    @(posedge clk) disable iff (!rst_n) state == DONE |-> ##1 initialize ##1 !initialize;
  endproperty
  assert property (initialize_high) else $error("Initialize signal is not high for one clock cycle after start");
  cover property (initialize_high); // $display("Checked: Initialize signal is high for one clock cycle after start");

  // Set band_pack_start when band_pack_count is zero
  property band_pack_start_on_zero;
    @(posedge clk) disable iff (!rst_n) band_pack_valid && band_pack_count == 0 |-> band_pack_start;
  endproperty
  assert property (band_pack_start_on_zero) else $error("Band pack start signal is not high when band pack count is zero");
  cover property (band_pack_start_on_zero); // $display("Checked: Band pack start signal is high when band pack count is zero");

  // Set band_pack_last when band_pack_count is equal to band_pack_threshold - 1
  property band_pack_last_on_threshold;
    @(posedge clk) disable iff (!rst_n) band_pack_valid && band_pack_count == band_pack_threshold - 1 |-> band_pack_last;
  endproperty
  assert property (band_pack_last_on_threshold) else $error("Band pack last signal is not high when band pack count is equal to band pack threshold - 1");
  cover property (band_pack_last_on_threshold); // $display("Checked: Band pack last signal is high when band pack count is equal to band pack threshold - 1");

  // Set band_pack_valid next clock cycle after read from both FIFOs
  property band_pack_valid_after_fifo_read;
    @(posedge clk) disable iff (!rst_n) fifo_both_read_en |-> ##1 band_pack_valid;
  endproperty
  assert property (band_pack_valid_after_fifo_read) else $error("Band pack valid signal is not high next clock cycle after read from both FIFOs");
  cover property (band_pack_valid_after_fifo_read); // $display("Checked: Band pack valid signal is high next clock cycle after read from both FIFOs");

  // Increment band_pack_count after band_pack_last
  property inc_band_pack_count;
    @(posedge clk) disable iff (!rst_n) band_pack_valid && !band_pack_last |-> ##1 (band_pack_count == $past(band_pack_count) + 1);
  endproperty
  assert property (inc_band_pack_count) else $error("Band pack count is not incremented correctly");
  cover property (inc_band_pack_count); // $display("Checked: Band pack count is incremented correctly");

  // Reset band_pack_count after band_pack_last
  property reset_band_pack_count;
    @(posedge clk) disable iff (!rst_n) band_pack_valid && band_pack_last |-> ##1 (band_pack_count == 0);
  endproperty
  assert property (reset_band_pack_count) else $error("Band pack count is not reset after last band pack");
  cover property (reset_band_pack_count); // $display("Checked: Band pack count is reset after last band pack");

endmodule
