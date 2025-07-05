`timescale 1ns / 1ps

module hsid_mse_batch_2 #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter WORD_WIDTH = DATA_WIDTH * 2,
    parameter DATA_WIDTH_SUM = DATA_WIDTH * 2
  ) (
    input logic clk,
    input logic rst_n,

    input logic [WORD_WIDTH-1:0] data_vctr_1, // Input vctr 1 with 4 elements
    input logic [WORD_WIDTH-1:0] data_vctr_2, // Input vctr 2 with 4 elements

    output logic [DATA_WIDTH_SUM-1:0] data_sum_out // Output sum
  );

  logic [DATA_WIDTH_SUM-1:0] sq_df_r1; // Output for the square difference module
  logic [DATA_WIDTH_SUM-1:0] sq_df_r2;

  hsid_sq_df #(
    .DATA_WIDTH(DATA_WIDTH)
  ) sq_df_p1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_v1(data_vctr_1[DATA_WIDTH-1:0]), // First element of vector 1
    .data_in_v2(data_vctr_2[DATA_WIDTH-1:0]), // First element of vector 2
    .data_out(sq_df_r1) // Output for first squared difference
  );

  hsid_sq_df #(
    .DATA_WIDTH(DATA_WIDTH)
  ) sq_df_p2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_v1(data_vctr_1[WORD_WIDTH-1:DATA_WIDTH]), // Second element of vector 1
    .data_in_v2(data_vctr_2[WORD_WIDTH-1:DATA_WIDTH]), // Second element of vector 2
    .data_out(sq_df_r2) // Output for second squared difference
  );

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      data_sum_out <= 0; // Reset output sum
    end else begin
      data_sum_out <= sq_df_r1 + sq_df_r2; // Compute the sum of squared differences
    end
  end

endmodule