`timescale 1ns / 1ps

import hsi_mse_pkg::*;

module mse_4_tb;

  localparam int DATA_WIDTH = 16; // Define the data width for the testbench
  localparam int WORD_WIDTH = DATA_WIDTH*4;
  localparam int DATA_WIDTH_SUM = DATA_WIDTH*2;

  reg clk;
  reg rst_n;
  reg [WORD_WIDTH-1:0] data_vctr_1;
  reg [WORD_WIDTH-1:0] data_vctr_2;
  wire [DATA_WIDTH_SUM-1:0] data_sum_out;

  mse_4 #(
    .DATA_WIDTH(DATA_WIDTH),
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH_SUM(DATA_WIDTH_SUM)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_vctr_1(data_vctr_1),
    .data_vctr_2(data_vctr_2),
    .data_sum_out(data_sum_out)
  );

  initial
  begin
    clk = 1;
    rst_n = 1;
    data_vctr_1 = 0;
    data_vctr_2 = 0;

    #10 rst_n = 0; // Reset the DUT
    #10 rst_n = 1; // Release reset

    // Test case 1: Vectors with elements [5, 3, 2, 1] and [3, 2, 1, 0]
    data_vctr_1 = {16'h5, 16'h3, 16'h2, 16'h1}; // 5, 3, 2, 1
    data_vctr_2 = {16'h3, 16'h2, 16'h1, 16'h0}; // 3, 2, 1, 0
    #40;
    if (data_sum_out !== 7) begin // Expected output: (5-3)^2 + (3-2)^2 + (2-1)^2 + (1-0)^2 = 4 + 1 + 1 + 1 = 7
      $display("Test case 1 failed: expected 7, got %0d", data_sum_out);
    end else begin
      $display("Test case 1 passed");
    end

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule