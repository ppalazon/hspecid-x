`timescale 1ns / 1ps

import hsid_pkg::*;

/*
 @WAVEDROM_START
 { signal: [
 { name: "clk",            wave: "p............." },
 { name: "rst_n",          wave: "l............." },
 { name: "clear",          wave: "l............." },
 { name: "initial_acc_en", wave: "lhl....hl....." },
 { name: "initial_acc",    wave: "x2x....2x.....", data: ['0', '10'] },
 { name: "data_in_valid",  wave: "lh.........l.." },
 { name: "data_in_a",      wave: "x3333336666x..", data: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] },
 { name: "data_in_b",      wave: "x7777779999x..", data: ['7', '2', '2', '6', '1', '7', '5', '7', '3', '9'] },
 { name: "data_in_last",   wave: "l.....hl..hl.." },
 { name: "acc_valid",      wave: "l..h.........l" },
 { name: "acc_value",      wave: "x..4444445555x", data: ['49', '50', '50', '59', '68', '72', '11', '11', '36', '36'] },
 { name: "acc_last",       wave: "l.......hl..hl" },
 { name: "acc_of",         wave: "l............." },
 ]}
 @WAVEDROM_END
 */
module hsid_sq_df_acc #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // HSP Data width
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // HSP Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC // HSP Data width for accumulator, larger than DATA_WIDTH
  ) (
    input logic clk,
    input logic rst_n,

    input logic clear,

    input logic initial_acc_en, // Enable initial accumulator value
    input logic [DATA_WIDTH_ACC-1:0] initial_acc, // Initial accumulator value

    input logic data_in_valid, // Valid input values
    input logic [DATA_WIDTH-1:0] data_in_a, // Input vector 1
    input logic [DATA_WIDTH-1:0] data_in_b, // Input vector 2
    input logic data_in_last,

    output logic acc_valid, // Output enable signal
    output logic [DATA_WIDTH_ACC-1:0] acc_value, // Output result
    output logic acc_last, // Output band counter
    output logic acc_of // Output overflow flag
  );

  logic stage_1_en, stage_2_en; // Enable signals for pipeline stages
  logic acc_1_en, acc_2_en; // Enable signals for accumulators
  logic [DATA_WIDTH_ACC-1:0] acc_1, acc_2; // Accumulators for pipeline stages
  logic last_1, last_2; // Band counter for HSP bands, using one extra bit to avoid overflow

  logic signed [DATA_WIDTH:0] diff; // Difference between bands, using one extra bit to avoid overflow / underflow
  logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result, using double the width of the input data
  logic [DATA_WIDTH_ACC:0] acc_w_of; // Accumulator for the final stage
  logic acc_reg_of; // Registered overflow flag for the accumulator

  assign acc_of = acc_reg_of || acc_w_of[DATA_WIDTH_ACC]; // Overflow flag for the accumulator
  assign acc_value = acc_w_of[DATA_WIDTH_ACC-1:0]; // Output accumulated value

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reset_values();
    end else begin
      if (clear) begin
        reset_values();
      end else begin
        if (data_in_valid) begin : diff_stage
          stage_1_en <= 1;
          acc_1_en <= initial_acc_en; // Enable initial accumulator value
          acc_1 <= initial_acc; // Set initial accumulator value
          last_1 <= data_in_last; // Capture last flag for stage 1
          diff <= data_in_a - data_in_b; // Compute difference, with extra bit you don't have to worry about overflow
        end else begin
          stage_1_en <= 0; // Disable stage 1
          // acc_1_en <= 0; // Disable initial accumulator value
          // last_1 <= 0;
        end
        if (stage_1_en) begin : square_diff_stage
          stage_2_en <= 1;
          acc_2_en <= acc_1_en; // Propagate enable signal for accumulator
          acc_2 <= acc_1; // Propagate accumulator value
          last_2 <= last_1; // Propagate last flag for stage 2
          mult <= diff * diff; // Compute squared difference and accumulate
        end else begin
          stage_2_en <= 0; // Disable stage 2
          // acc_2_en <= 0; // Disable accumulator
          // last_2 <= 0;
        end
        if (stage_2_en) begin : accumulate_stage
          acc_valid <= 1; // Enable output when valid
          acc_last <= last_2; // Propagate band counter for output
          if(acc_2_en) begin
            acc_reg_of <= 0;
            acc_w_of <= acc_2 + mult; // Add to initial accumulator value
          end else begin
            if (acc_w_of[DATA_WIDTH_ACC]) begin
              acc_reg_of <= 1; // Register overflow flag
            end
            acc_w_of <= acc_w_of + mult; // Add to initial accumulator value
          end
        end else begin
          acc_valid <= 0; // Disable output when not valid
          acc_last <= 0; // Reset band counter for output
        end
      end
    end
  end

  task reset_values();
    diff <= 0; // Reset difference
    mult <= 0; // Reset multiplication result
    stage_1_en <= 0; // Reset stage 2
    stage_2_en <= 0; // Reset stage 3
    acc_1 <= 0; // Reset stage 1 accumulator
    acc_2 <= 0; // Reset stage 2 accumulator
    acc_1_en <= 0; // Disable initial accumulator value
    acc_2_en <= 0; // Disable stage 2 accumulator
    last_1 <= 0; // Reset band counter for stage 1
    last_2 <= 0; // Reset band counter for stage 2
    acc_w_of <= 0; // Reset accumulator with overflow bit
    acc_reg_of <= 0; // Reset registered overflow flag
    acc_last <= 0; // Reset band counter output
    acc_valid <= 0; // Disable output
  endtask
endmodule