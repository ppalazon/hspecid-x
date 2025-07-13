`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_top_fsm #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    parameter ELEMENTS = HSI_BANDS / 2, // Number of elements in the vector
    localparam ELEMENTS_ADDR = $clog2(ELEMENTS),  // Address width for elements
    localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    input [HSI_BANDS_ADDR-1:0] pixel_bands,  // HSI bands to process
    input [HSI_LIBRARY_SIZE_ADDR-1:0] library_size,  // Size of the HSI library
    input [WORD_WIDTH-1:0] captured_pixel_addr,  // Address for captured pixel data
    input [WORD_WIDTH-1:0] library_pixel_addr,  // Address for library pixel data
    input logic start,  // Start signal to initiate the FSM
    input logic clear,  // Clear signal to reset MSE values

    // OBI interface signals
    output logic [WORD_WIDTH-1:0] obi_initial_addr,
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] obi_limit_in,
    output logic obi_start,
    input wire obi_done,

    output logic error  // Error flag
  );

  // Elements bands
  logic [ELEMENTS_ADDR-1:0] elements_bands;

  // Assign Interrupt output

  assign elements_bands = (pixel_bands / 2);

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
        obi_limit_in <= { {(HSI_LIBRARY_SIZE_ADDR-ELEMENTS_ADDR){1'b0}}, elements_bands };
        obi_start <= 1'b1;
      end else if (current_state == READ_CAPTURED) begin
        obi_start <= 1'b0;
      end else if (current_state == START_READ_LIBRARY) begin
        obi_initial_addr <= library_pixel_addr;
        obi_limit_in <= elements_bands * library_size;
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