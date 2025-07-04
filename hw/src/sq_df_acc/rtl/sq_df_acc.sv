`timescale 1ns / 1ps

import hsid_pkg::*;

module sq_df_acc #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = 32, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = 48, // Data width for accumulator, larger than DATA_WIDTH
    parameter HSI_LIBRARY_SIZE = 256, // Size of the HSI library
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE) // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    input logic initial_acc_en,                   // Enable initial accumulator value
    input logic [DATA_WIDTH_ACC-1:0] initial_acc, // Initial accumulator value

    input logic data_in_valid, // Valid input values
    input logic signed [DATA_WIDTH-1:0] data_in_a, // Input vector 1
    input logic signed [DATA_WIDTH-1:0] data_in_b, // Input vector 2
    input logic data_in_last,
    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] data_in_ref, // Reference vector for sum

    output logic acc_valid, // Output enable signal
    output logic [DATA_WIDTH_ACC-1:0] acc_value, // Output result
    output logic acc_last, // Output band counter
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] acc_ref // Reference vector for sum
  );

  // logic signed [DATA_WIDTH-1:0] data_in_v1_reg, data_in_v2_reg; // Register for input vector 1
  // logic stage_1_en, stage_2_en, stage_3_en; // Enable signals for pipeline stages
  // logic acc_1_en, acc_2_en, acc_3_en; // Enable signals for accumulators
  // logic [DATA_WIDTH_ACC-1:0] acc_1, acc_2, acc_3; // Accumulators for pipeline stages
  // logic last_1, last_2, last_3; // Band counter for HSI bands, using one extra bit to avoid overflow
  // logic [HSI_LIBRARY_SIZE_ADDR-1:0] ref_1, ref_2, ref_3; // Band counter output for HSI bands

  logic stage_2_en, stage_3_en; // Enable signals for pipeline stages
  logic acc_2_en, acc_3_en; // Enable signals for accumulators
  logic [DATA_WIDTH_ACC-1:0] acc_2, acc_3; // Accumulators for pipeline stages
  logic last_2, last_3; // Band counter for HSI bands, using one extra bit to avoid overflow
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] ref_2, ref_3; // Band counter output for HSI bands


  logic signed [DATA_WIDTH:0] diff; // Difference between elements, using one extra bit for overflow
  logic [DATA_WIDTH_MUL-1:0] mult;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      diff <= 0; // Reset difference
      mult <= 0; // Reset multiplication result
      // data_in_v1_reg <= 0; // Reset input vector 1 register
      // data_in_v2_reg <= 0; // Reset input vector 2 register
      // stage_1_en <= 0; // Reset stage 1
      stage_2_en <= 0; // Reset stage 2
      stage_3_en <= 0; // Reset stage 3
      // acc_1 <= 0; // Reset stage 0 accumulator
      acc_2 <= 0; // Reset stage 1 accumulator
      acc_3 <= 0; // Reset stage 2 accumulator
      // acc_1_en <= 0; // Disable stage 0 accumulator
      acc_2_en <= 0; // Disable initial accumulator value
      acc_3_en <= 0; // Disable stage 2 accumulator
      // last_1 <= 0; // Reset band counter for stage 0
      last_2 <= 0; // Reset band counter for stage 1
      last_3 <= 0; // Reset band counter for stage 2
      // ref_1 <= 0; // Reset reference vector for stage 0
      ref_2 <= 0; // Reset reference vector for stage 1
      ref_3 <= 0; // Reset reference vector for stage 2
      acc_last <= 0; // Reset band counter output
      acc_value <= 0; // Reset output data
      acc_valid <= 0; // Disable output
      acc_ref <= 0; // Reset reference vector for sum
    end else begin
      // if (data_in_valid) begin : read_stage
      //   stage_1_en <= 1;
      //   acc_1_en <= initial_acc_en; // Enable initial accumulator value
      //   acc_1 <= initial_acc; // Set initial accumulator value
      //   data_in_v1_reg <= data_in_a; // Capture input vector 1
      //   data_in_v2_reg <= data_in_b; // Capture input vector 2
      //   last_1 <= data_in_last; // Capture last flag for stage 1
      //   ref_1 <= data_in_ref; // Capture reference vector for stage 1
      // end else begin
      //   stage_1_en <= 0; // Disable stage 1
      //   acc_2_en <= 0; // Disable initial accumulator value
      //   last_1 <= 0;
      // end
      // if (stage_1_en) begin : diff_stage
      //   stage_2_en <= 1;
      //   acc_2_en <= acc_1_en; // Enable initial accumulator value
      //   acc_2 <= acc_1; // Set initial accumulator value
      //   diff <= data_in_v1_reg - data_in_v2_reg; // Compute difference
      //   last_2 <= last_1; // Capture last flag for stage 1
      //   ref_2 <= ref_1; // Capture reference vector for stage 1
      // end else begin
      //   stage_2_en <= 0; // Disable stage 1
      //   acc_2_en <= 0; // Disable initial accumulator value
      //   last_2 <= 0;
      // end
      if (data_in_valid) begin : diff_stage
        stage_2_en <= 1;
        acc_2_en <= initial_acc_en; // Enable initial accumulator value
        acc_2 <= initial_acc; // Set initial accumulator value
        diff <= data_in_a - data_in_b; // Compute difference
        last_2 <= data_in_last; // Capture last flag for stage 1
        ref_2 <= data_in_ref; // Capture reference vector for stage 1
      end else begin
        stage_2_en <= 0; // Disable stage 1
        acc_2_en <= 0; // Disable initial accumulator value
        last_2 <= 0;
      end
      if (stage_2_en) begin : square_diff_stage
        stage_3_en <= 1;
        acc_3_en <= acc_2_en; // Propagate enable signal for accumulator
        acc_3 <= acc_2; // Propagate accumulator value
        mult <= diff * diff; // Compute squared difference and accumulate
        last_3 <= last_2; // Propagate last flag for stage 2
        ref_3 <= ref_2; // Propagate reference vector for stage 2
      end else begin
        stage_3_en <= 0; // Disable stage 2
        acc_3_en <= 0; // Disable accumulator
        last_3 <= 0;
      end
      if (stage_3_en) begin : accumulate_stage
        acc_valid <= 1; // Enable output when all stages are ready
        acc_last <= last_3; // Propagate band counter for output
        acc_ref <= ref_3; // Propagate reference vector for output
        if(acc_3_en) begin
          acc_value <= acc_3 + mult; // Add to initial accumulator value
        end else begin
          acc_value <= acc_value + mult; // Add to initial accumulator value
        end
      end else begin
        acc_valid <= 0;
        acc_last <= 0;
      end
    end
  end
endmodule