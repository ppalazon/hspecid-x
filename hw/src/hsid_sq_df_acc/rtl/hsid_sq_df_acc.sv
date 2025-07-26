`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_sq_df_acc #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    input logic clean,

    input logic initial_acc_en, // Enable initial accumulator value
    input logic [DATA_WIDTH_ACC-1:0] initial_acc, // Initial accumulator value

    input logic data_in_valid, // Valid input values
    input logic [DATA_WIDTH-1:0] data_in_a, // Input vector 1
    input logic [DATA_WIDTH-1:0] data_in_b, // Input vector 2
    input logic data_in_last,
    input logic [HSP_LIBRARY_WIDTH-1:0] data_in_ref, // Reference vector for sum

    output logic acc_valid, // Output enable signal
    output logic [DATA_WIDTH_ACC-1:0] acc_value, // Output result
    output logic acc_last, // Output band counter
    output logic [HSP_LIBRARY_WIDTH-1:0] acc_ref, // Reference vector for sum
    output logic acc_of // Output overflow flag
  );

  logic stage_1_en, stage_2_en, stage_3_en; // Enable signals for pipeline stages
  logic acc_1_en, acc_2_en; // Enable signals for accumulators
  logic [DATA_WIDTH_ACC-1:0] acc_1, acc_2, acc_3; // Accumulators for pipeline stages
  logic last_1, last_2, last_3; // Band counter for HSI bands, using one extra bit to avoid overflow
  logic [HSP_LIBRARY_WIDTH-1:0] ref_1, ref_2, ref_3; // Band counter output for HSI bands
  logic acc_of_3; // Overflow flags for pipeline stages

  logic signed [DATA_WIDTH:0] diff; // Difference between elements, using one extra bit to avoid overflow / underflow
  logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result, using double the width of the input data

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reset_values();
    end else begin
      if (clean) begin
        reset_values();
      end else begin
        if (data_in_valid) begin : diff_stage
          stage_1_en <= 1;
          acc_1_en <= initial_acc_en; // Enable initial accumulator value
          acc_1 <= initial_acc; // Set initial accumulator value
          last_1 <= data_in_last; // Capture last flag for stage 1
          ref_1 <= data_in_ref; // Capture reference vector for stage 1
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
          ref_2 <= ref_1; // Propagate reference vector for stage 2
          mult <= diff * diff; // Compute squared difference and accumulate
        end else begin
          stage_2_en <= 0; // Disable stage 2
          // acc_2_en <= 0; // Disable accumulator
          // last_2 <= 0;
        end
        if (stage_2_en) begin : accumulate_stage
          stage_3_en <= 1;
          last_3 <= last_2;
          ref_3 <= ref_2;
          if(acc_2_en) begin
            acc_of <= 0; // Reset overflow flag on initial accumulator value
            {acc_of_3, acc_3} <= acc_2 + mult; // Add to initial accumulator value
          end else begin
            {acc_of_3, acc_3} <= acc_3 + mult; // Add to initial accumulator value
          end
        end else begin
          stage_3_en <= 0; // Disable stage 3
          // acc_3_en <= 0; // Disable accumulator
        end
        if (stage_3_en) begin
          acc_valid <= !(acc_of || acc_of_3); // If there has been overflow in the last stage or in any other stage
          if (acc_of_3) begin
            acc_of <= 1;
          end
          acc_value <= acc_3; // Output accumulated value
          acc_last <= last_3; // Propagate band counter for output
          acc_ref <= ref_3; // Propagate reference vector for output
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
    stage_3_en <= 0; // Reset stage 3
    acc_1 <= 0; // Reset stage 1 accumulator
    acc_2 <= 0; // Reset stage 2 accumulator
    acc_3 <= 0; // Reset stage 3 accumulator
    acc_1_en <= 0; // Disable initial accumulator value
    acc_2_en <= 0; // Disable stage 2 accumulator
    last_1 <= 0; // Reset band counter for stage 1
    last_2 <= 0; // Reset band counter for stage 2
    last_3 <= 0; // Reset band counter for stage 3
    ref_1 <= 0; // Reset reference vector for stage 1
    ref_2 <= 0; // Reset reference vector for stage 2
    ref_3 <= 0; // Reset reference vector for stage 3
    acc_of_3 <= 0; // Reset overflow flag for accumulator
    acc_last <= 0; // Reset band counter output
    acc_value <= 0; // Reset output data
    acc_valid <= 0; // Disable output
    acc_ref <= 0; // Reset reference vector for sum
    acc_of <= 0; // Reset overflow flag for accumulator
  endtask
endmodule