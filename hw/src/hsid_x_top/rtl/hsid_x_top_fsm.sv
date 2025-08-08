`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_top_fsm #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
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
    output logic interrupt,  // Idle signal indicating FSM is not processing

    // OBI interface signals
    output logic [WORD_WIDTH-1:0] obi_initial_addr,
    output logic [MEM_ACCESS_WIDTH-1:0] obi_limit_in,
    output logic obi_start,
    input wire obi_done
  );

  // Elements bands
  logic [HSP_BANDS_WIDTH-1:0] cfg_hsp_bands;  // Number of pixel band packs
  logic [HSP_LIBRARY_WIDTH-1:0] cfg_hsp_library_size;  // Size of the HSI library
  logic [HSP_BANDS_WIDTH-1:0] cfg_band_pack_threshold;

  // Cancel signal to stop reading from OBI
  logic cancel_read;

  // Assignations
  assign cancel_read = clear || error || done;
  assign interrupt = done || error;  // Interrupt signal is high when done or error

  hsid_x_top_t current_state = HXT_IDLE, next_state = HXT_START_READ_CAPTURED;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= HXT_IDLE;
      cfg_hsp_bands <= '0;
      cfg_hsp_library_size <= '0;
      cfg_band_pack_threshold <= '0;
      obi_initial_addr <= 0;
      obi_limit_in <= 1;
      obi_start <= 1'b0;
    end else begin
      current_state <= next_state;  // Update current state
      if (current_state == HXT_IDLE) begin
        obi_initial_addr <= 0;
        obi_limit_in <= 1;
        obi_start <= 1'b0;
      end else if (current_state == HXT_CONFIG) begin
        cfg_hsp_bands <= hsp_bands;  // Set HSP bands to process
        cfg_hsp_library_size <= hsp_library_size;  // Set HSP library size
        cfg_band_pack_threshold <= (hsp_bands + 1) / 2;
      end else if (current_state == HXT_START_READ_CAPTURED) begin
        obi_initial_addr <= captured_pixel_addr;
        obi_limit_in <= { {(MEM_ACCESS_WIDTH-HSP_BANDS_WIDTH){1'b0}}, cfg_band_pack_threshold };
        obi_start <= 1'b1;
      end else if (current_state == HXT_READ_CAPTURED) begin
        obi_start <= 1'b0;
      end else if (current_state == HXT_START_READ_LIBRARY) begin
        obi_initial_addr <= library_pixel_addr;
        obi_limit_in <= cfg_band_pack_threshold * hsp_library_size;
        obi_start <= 1'b1;
      end else if (current_state == HXT_READ_LIBRARY) begin
        obi_start <= 1'b1;
      end
    end
  end

  always_comb begin
    case (current_state)
      HXT_IDLE: begin
        next_state = start ? HXT_CONFIG : HXT_IDLE;
      end
      HXT_CONFIG: begin
        next_state = cancel_read ? HXT_IDLE : HXT_START_READ_CAPTURED;
      end
      HXT_START_READ_CAPTURED: begin
        next_state = cancel_read ? HXT_IDLE : HXT_READ_CAPTURED;
      end
      HXT_READ_CAPTURED: begin
        next_state = cancel_read ? HXT_IDLE : (obi_done ? HXT_START_READ_LIBRARY : HXT_READ_CAPTURED);
      end
      HXT_START_READ_LIBRARY: begin
        next_state = cancel_read ? HXT_IDLE : HXT_READ_LIBRARY;
      end
      HXT_READ_LIBRARY: begin
        next_state = cancel_read ? HXT_IDLE : (obi_done ? HXT_IDLE : HXT_READ_LIBRARY);
      end
      default: begin
        next_state = HXT_IDLE;
      end
    endcase
  end

endmodule