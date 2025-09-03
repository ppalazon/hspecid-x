`timescale 1ns / 1ps

import hsid_pkg::*;  // Import the package for HSI MSE

module hsid_main_fsm #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Number of bits to represent vector length
  ) (
    input logic clk,
    input logic rst_n,

    input logic clear,

    // Input vector data
    input logic band_data_in_valid,  // Enable input sample data
    input logic [WORD_WIDTH-1:0] band_data_in, // Input sample word data

    // Library size input
    input logic [HSP_BANDS_WIDTH-1:0] hsp_bands,  // HSP bands to process
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_library_size,  // Length of the vectors

    // Configured parameters
    output logic [HSP_BANDS_WIDTH-1:0] cfg_band_pack_threshold,  // HSP bands packs to process
    output logic [HSP_BANDS_WIDTH-1:0] cfg_hsp_bands,  // HSP bands packs to process

    // Fifo status signals
    input logic fifo_captured_complete,  // Full signal for measure vector FIFO
    input logic fifo_captured_empty,  // Empty signal for measure vector FIFO
    input logic fifo_ref_empty,  // Empty signal for output data FIFO
    input logic fifo_ref_full,  // Full signal for output data FIFO

    // FIFO Control signals
    output logic [WORD_WIDTH-1:0] fifo_captured_data_in,
    output logic fifo_captured_write_en,
    output logic fifo_ref_write_en,

    // MSE signals
    input logic mse_valid,
    input logic [HSP_LIBRARY_WIDTH-1:0] mse_ref,
    input logic mse_comparison_valid,

    // Current state
    // output hsid_main_state_t state,
    output logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_count,
    output logic band_pack_start,  // Start vector processing signal
    output logic band_pack_last,  // Last vector processing signal
    output logic band_pack_valid,  // Element valid signal
    output logic fifo_both_read_en,
    output logic initialize,

    // Block interface for handshake signals
    input logic start,
    output logic done,
    output logic idle,
    output logic ready,
    output logic error,
    output logic cancelled
  );

  // Internal state machine states
  hsid_main_state_t current_state = HM_IDLE, next_state = HM_IDLE;
  logic [HSP_LIBRARY_WIDTH-1:0] cfg_hsp_library_size;
  logic cfg_fail;  // Configuration failure flag
  logic [HSP_BANDS_WIDTH-1:0] ref_band_pack_count;
  // logic [HSP_BANDS_WIDTH-1:0] cap_band_pack_count;
  // logic cap_read_finished;
  logic hsp_ref_last;

  // Combinational assignments
  assign fifo_both_read_en = (current_state == HM_COMPUTE_MSE && next_state == HM_COMPUTE_MSE && !fifo_ref_empty && !fifo_captured_empty);
  assign hsp_ref_last = (current_state == HM_COMPUTE_MSE && hsp_ref_count == cfg_hsp_library_size - 1);
  assign band_pack_start = (current_state == HM_COMPUTE_MSE && band_pack_valid && ref_band_pack_count == 0);
  assign band_pack_last = (current_state == HM_COMPUTE_MSE && band_pack_valid && ref_band_pack_count == cfg_band_pack_threshold - 1);
  // assign state = current_state;
  assign cfg_fail = (current_state == HM_CONFIG && hsp_bands < 7 || hsp_library_size == 0);
  // Assigns statements
  // assign cap_read_finished = (current_state == HM_READ_HSP_CAPTURED && cap_band_pack_count == cfg_band_pack_threshold);
  assign fifo_captured_write_en = (current_state == HM_READ_HSP_CAPTURED && next_state == HM_READ_HSP_CAPTURED && band_data_in_valid); //&& cap_band_pack_count < cfg_band_pack_threshold);
  assign fifo_captured_data_in = current_state == HM_READ_HSP_CAPTURED ? band_data_in : '0; //(state == COMPUTE_MSE ? fifo_measure_data_out : '0);
  assign fifo_ref_write_en = (current_state == HM_COMPUTE_MSE && next_state == HM_COMPUTE_MSE && band_data_in_valid);
  assign initialize = (current_state == HM_DONE || current_state == HM_ERROR);

  // Check measure vector FIFO status

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= HM_IDLE;  // Reset to IDLE state
      reset_values();
    end else begin
      current_state <= next_state;  // Transition to next state
      if (current_state == HM_CLEAR || current_state == HM_DONE || current_state == HM_ERROR) begin
        reset_values();
      end else if (current_state == HM_CONFIG) begin
        cfg_hsp_bands <= hsp_bands;  // Set HSP bands to process
        cfg_hsp_library_size <= hsp_library_size;  // Set HSP library size
        cfg_band_pack_threshold <= (hsp_bands + 1) / 2;
        // end else if (current_state == HM_READ_HSP_CAPTURED) begin
        //   if (band_data_in_valid) begin
        //     cap_band_pack_count <= cap_band_pack_count + 1;
        //   end
      end else begin
        band_pack_valid <= fifo_both_read_en; // After read from both FIFOs, set band_pack_valid
        // finished_library <= hsp_ref_last & band_pack_last;
        if (band_pack_valid) begin
          if (ref_band_pack_count == cfg_band_pack_threshold - 1) begin
            ref_band_pack_count <= 0;  // Reset element count when threshold is reached
          end else begin
            ref_band_pack_count <= ref_band_pack_count + 1;
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
      HM_IDLE: begin
        idle = 1; ready = 0; done = 0; error = 0; cancelled = 0;
        next_state = !clear && start ? HM_CONFIG : HM_IDLE; // Give priority to clear signal
      end
      HM_CLEAR: begin
        idle = 0; ready = 0; done = 0; error = 0; cancelled = 1;
        next_state = HM_IDLE;  // Transition to IDLE after clearing
      end
      HM_CONFIG: begin
        idle = 0; ready = 0; done = 0; error = 0; cancelled = 0;
        next_state = clear ? HM_CLEAR : (cfg_fail ? HM_ERROR : HM_READ_HSP_CAPTURED);
      end
      HM_ERROR: begin
        idle = 0; ready = 0; done = 0; error = 1; cancelled = 0;  // Error state, no further processing
        next_state = HM_IDLE;  // Stay in error state until cleared
      end
      HM_READ_HSP_CAPTURED: begin
        idle = 0; ready = 1; done = 0; error = 0; cancelled = 0;
        next_state = clear ? HM_CLEAR : (fifo_captured_complete ? HM_COMPUTE_MSE : HM_READ_HSP_CAPTURED);
      end
      HM_COMPUTE_MSE: begin
        idle = 0; ready = !fifo_ref_full; done = 0; error = 0; cancelled = 0;
        next_state = clear ? HM_CLEAR : (hsp_ref_last & band_pack_last ? HM_WAIT_MSE : HM_COMPUTE_MSE);
      end
      HM_WAIT_MSE: begin
        idle = 0; ready = 0; done = 0; error = 0; cancelled = 0;
        next_state = clear ? HM_CLEAR : (mse_valid && mse_ref == cfg_hsp_library_size - 1 ? HM_COMPARE_MSE : HM_WAIT_MSE);
      end
      HM_COMPARE_MSE: begin
        idle = 0; ready = 0; done = 0; error = 0; cancelled = 0;
        next_state = clear ? HM_CLEAR : (mse_comparison_valid ? HM_DONE : HM_COMPARE_MSE);
      end
      HM_DONE: begin
        idle = 0; ready = 0; done = 1; error = 0; cancelled = 0;
        next_state = HM_IDLE;
      end
      default: begin
        idle = 1; ready = 0; done = 0; error = 0; cancelled = 0;
        next_state = HM_IDLE;
      end
    endcase
  end

  task reset_values();
    begin
      // cap_band_pack_count <= 0;
      ref_band_pack_count <= 0;
      hsp_ref_count <= 0;
      band_pack_valid <= 0;
      // finished_library <= 0;
      cfg_band_pack_threshold <= {{HSP_BANDS_WIDTH{1'b1}}};  // Max value for threshold to avoid false captured FIFO complete
      cfg_hsp_library_size <= {{HSP_LIBRARY_WIDTH{1'b1}}}; // Max value for library size to avoid false last hsp
      cfg_hsp_bands <= {{HSP_BANDS_WIDTH{1'b1}}}; // Max value for HSP bands to avoid false last hsp bands
    end
  endtask

endmodule