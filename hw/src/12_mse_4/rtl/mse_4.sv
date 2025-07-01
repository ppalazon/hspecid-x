`timescale 1ns / 1ps

module mse_4 #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter WORD_WIDTH = DATA_WIDTH * 4,
    parameter DATA_WIDTH_SUM = DATA_WIDTH * 2
  ) (
    input logic clk,
    input logic rst_n,

    input logic [WORD_WIDTH-1:0] data_vctr_1, // Input vctr 1 with 4 elements
    input logic [WORD_WIDTH-1:0] data_vctr_2, // Input vctr 2 with 4 elements

    output logic [DATA_WIDTH_SUM-1:0] data_sum_out // Output sum
  );

  logic [DATA_WIDTH_SUM-1:0] mse_2_r1; // Output for the squa
  logic [DATA_WIDTH_SUM-1:0] mse_2_r2;

  // Instantiate two mse_2 modules for the first two pairs of elements
  mse_2 #(
    .DATA_WIDTH(DATA_WIDTH)
  ) mse_2_p1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_vctr_1(data_vctr_1[DATA_WIDTH*2-1:0]), // First two elements of vector 1
    .data_vctr_2(data_vctr_2[DATA_WIDTH*2-1:0]), // First two elements of vector 2
    .data_sum_out(mse_2_r1) // Output for first squared difference
  );

  mse_2 #(
    .DATA_WIDTH(DATA_WIDTH)
  ) mse_2_p2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_vctr_1(data_vctr_1[WORD_WIDTH-1:DATA_WIDTH*2]), // Second two elements of vector 1
    .data_vctr_2(data_vctr_2[WORD_WIDTH-1:DATA_WIDTH*2]), // Second two elements of vector 2
    .data_sum_out(mse_2_r2) // Output for second squared difference
  );

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      data_sum_out <= 0; // Reset output sum
    end else begin
      data_sum_out <= mse_2_r1 + mse_2_r2; // Compute the sum of squared differences
    end
  end

endmodule