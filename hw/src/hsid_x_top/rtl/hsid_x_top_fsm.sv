`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_top_fsm #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    input [HSP_BANDS_WIDTH-1:0] pixel_bands,  // HSP bands to process
    input [HSP_LIBRARY_WIDTH-1:0] library_size,  // Size of the HSI library
    input [WORD_WIDTH-1:0] captured_pixel_addr,  // Address for captured pixel data
    input [WORD_WIDTH-1:0] library_pixel_addr,  // Address for library pixel data
    input logic start,  // Start signal to initiate the FSM
    input logic clear,  // Clear signal to reset MSE values

    // OBI interface signals
    output logic [WORD_WIDTH-1:0] obi_initial_addr,
    output logic [HSP_LIBRARY_WIDTH-1:0] obi_limit_in,
    output logic obi_start,
    input wire obi_done,

    output logic error  // Error flag
  );

  localparam HSP_BAND_PACK_WIDTH = HSP_BANDS_WIDTH - $clog2(WORD_WIDTH / DATA_WIDTH);  // Address width for HSP bands

  // Elements bands
  logic [HSP_BAND_PACK_WIDTH-1:0] pixel_band_packs;

  // Assign Interrupt output

  assign pixel_band_packs = (pixel_bands / 2);

  hsid_x_obi_read_t current_state = OR_IDLE, next_state = START_READ_CAPTURED;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= OR_IDLE;
      error <= 1'b0;  // Reset error flag
      obi_initial_addr <= 0;
      obi_limit_in <= 1;
      obi_start <= 1'b0;
    end else begin
      current_state <= next_state;  // Update current state
      error <= 1'b0;  // Reset error flag
      if (current_state == OR_IDLE) begin
        obi_initial_addr <= 0;
        obi_limit_in <= 1;
        obi_start <= 1'b0;
      end else if (current_state == START_READ_CAPTURED) begin
        obi_initial_addr <= captured_pixel_addr;
        obi_limit_in <= { {(HSP_LIBRARY_WIDTH-HSP_BAND_PACK_WIDTH){1'b0}}, pixel_band_packs };
        obi_start <= 1'b1;
      end else if (current_state == READ_CAPTURED) begin
        obi_start <= 1'b0;
      end else if (current_state == START_READ_LIBRARY) begin
        obi_initial_addr <= library_pixel_addr;
        obi_limit_in <= pixel_band_packs * library_size;
        obi_start <= 1'b1;
      end else if (current_state == READ_LIBRARY) begin
        obi_start <= 1'b1;
      end
    end
  end

  always_comb begin
    case (current_state)
      OR_IDLE: begin
        next_state = start ? START_READ_CAPTURED : OR_IDLE;
      end
      START_READ_CAPTURED: begin
        next_state = READ_CAPTURED;
      end
      READ_CAPTURED: begin
        next_state = obi_done ? START_READ_LIBRARY : READ_CAPTURED;
      end
      START_READ_LIBRARY: begin
        next_state = READ_LIBRARY;
      end
      READ_LIBRARY: begin
        next_state = obi_done ? OR_IDLE : READ_LIBRARY;
      end
      default: begin
        next_state = OR_IDLE;
      end
    endcase
  end

endmodule