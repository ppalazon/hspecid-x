`timescale 1ns / 1ps

import hsid_pkg::*;  // Import the package for HSI MSE

module hsid_main_fsm #(
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
    output hsid_main_state_t state,
    output logic [HSP_BANDS_WIDTH-1:0] band_pack_count,
    output logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_count,
    output logic band_pack_start,  // Start vector processing signal
    output logic band_pack_last,  // Last vector processing signal
    output logic band_pack_valid,  // Element valid signal
    output logic finished_library,
    output logic hsp_ref_last,
    output logic fifo_both_read_en,
    output logic initialize,

    // Block interface for handshake signals
    input logic start,
    output logic done,
    output logic idle,
    output logic ready
  );

  assign fifo_both_read_en = (state == COMPUTE_MSE && !fifo_ref_empty && !fifo_captured_empty);
  assign hsp_ref_last = (hsp_ref_count == hsp_library_size - 1);
  assign band_pack_start = (band_pack_valid && band_pack_count == 0);
  assign band_pack_last = (band_pack_valid && band_pack_count == band_pack_threshold - 1);

  hsid_main_state_t current_state = IDLE, next_state = READ_HSP_CAPTURED;

  assign state = current_state;

  // Check measure vector FIFO status

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;  // Reset to IDLE state
      band_pack_count <= 0;  // Reset element count
      hsp_ref_count <= 0;  // Reset vector count
      band_pack_valid <= 0;  // Reset valid signal
      finished_library <= 0;  // Reset finished library flag
      initialize <= 0;  // Set initialize signal
    end else begin
      current_state <= next_state;  // Transition to next state
      if (current_state == DONE) begin : re_initialize
        hsp_ref_count <= 0;
        band_pack_valid <= 0;
        band_pack_count <= 0;
        finished_library <= 0;
        initialize <= 1;
      end else begin
        initialize <= 0;
        band_pack_valid <= fifo_both_read_en; // After read from both FIFOs, set band_pack_valid
        finished_library <= hsp_ref_last & band_pack_last;
        if (band_pack_valid) begin
          if (band_pack_count == band_pack_threshold - 1) begin
            band_pack_count <= 0;  // Reset element count when threshold is reached
          end else begin
            band_pack_count <= band_pack_count + 1;
          end
          if (band_pack_last) begin
            hsp_ref_count <= hsp_ref_count + 1;
          end
        end
      end
    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        idle = 1; ready = 0; done = 0;
        next_state = start ? READ_HSP_CAPTURED : IDLE;
      end
      READ_HSP_CAPTURED: begin
        idle = 0; ready = 1; done = 0;
        next_state = fifo_captured_complete ? COMPUTE_MSE : READ_HSP_CAPTURED;
      end
      COMPUTE_MSE: begin
        idle = 0; ready = !fifo_ref_full; done = 0;
        next_state = finished_library ? WAIT_MSE : COMPUTE_MSE;
      end
      WAIT_MSE: begin
        idle = 0; ready = 0; done = 0;
        next_state = mse_valid ? COMPARE_MSE : WAIT_MSE;
      end
      COMPARE_MSE: begin
        idle = 0; ready = 0; done = 0;
        next_state = mse_comparison_valid ? DONE : COMPARE_MSE;
      end
      DONE: begin
        idle = 0; ready = 0; done = 1;
        next_state = IDLE;
      end
      default: begin
        idle = 1; ready = 0; done = 0;
        next_state = IDLE;
      end
    endcase
  end

endmodule