`timescale 1ns / 1ps

import hsi_mse_pkg::*;

module hsi_mse_comp_tb;

  localparam WORD_WIDTH = 32;

  reg clk;
  reg rst_n;
  reg mse_in_valid;
  reg [WORD_WIDTH-1:0] mse_in;
  reg clear;  // Clear signal, not used in this test
  wire mse_out_valid;
  wire [WORD_WIDTH-1:0] mse_out_min;
  wire [WORD_WIDTH-1:0] mse_out_max;

  // Aux min and max values for comparison
  logic [WORD_WIDTH-1:0] aux_min = 32'hFFFFFFFF;  // Initialize aux_min to max value
  logic [WORD_WIDTH-1:0] aux_max = 32'h0;  // Initialize aux_max to min value

  hsi_mse_comp #(
    .WORD_WIDTH(WORD_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .mse_in_valid(mse_in_valid),
    .mse_out_valid(mse_out_valid),
    .mse_in(mse_in),
    .mse_out_min(mse_out_min),
    .mse_out_max(mse_out_max),
    .clear(clear)
  );

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsi_mse_comp_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    mse_in_valid = 0;
    mse_in = 0;
    clear = 0;

    #10 rst_n = 0;  // Reset the DUT
    #10 rst_n = 1;  // Release reset

    // First value: medium
    mse_in_valid = 1;
    mse_in = 32'h0000FFFF;  // Input MSE value
    #10;
    mse_in_valid = 0;  // Disable input MSE valid signal

    if (mse_out_valid && mse_out_min == 32'h0000FFFF && mse_out_max == 32'h0000FFFF) begin
      $display("MSE Out Valid: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
    end else begin
      $error("Comparison failed: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
    end

    // Second value: bigger
    mse_in_valid = 1;
    mse_in = 32'h000FFFFF;  // Input MSE value
    #10;
    mse_in_valid = 0;  // Disable input MSE valid signal

    if (mse_out_valid && mse_out_min == 32'h0000FFFF && mse_out_max == 32'h000FFFFF) begin
      $display("MSE Out Valid: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
    end else begin
      $error("Comparison failed: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
    end

    // Second value: smaller
    mse_in_valid = 1;
    mse_in = 32'h00000FFF;  // Input MSE value
    #10;
    mse_in_valid = 0;  // Disable input MSE valid signal

    if (mse_out_valid && mse_out_min == 32'h00000FFF && mse_out_max == 32'h000FFFFF) begin
      $display("MSE Out Valid: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
    end else begin
      $error("Comparison failed: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
    end

    // Clear the output
    clear = 1;
    #10;
    clear = 0;
    #10;

    for (int i = 0; i < 50; i++) begin
      mse_in_valid = $urandom % 2;
      mse_in = $urandom;  // Random MSE value
      if (mse_in_valid) begin
        aux_min = (mse_in <= aux_min) ? mse_in : aux_min;  // Update aux_min
        aux_max = (mse_in >= aux_max) ? mse_in : aux_max;
      end
      #10;

      if (mse_out_valid == mse_in_valid && mse_out_min == aux_min && mse_out_max == aux_max) begin
        $display("MSE Out Valid: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
      end else begin
        $error("MSE Out Invalid: MSE Min: %h, MSE Max: %h", mse_out_min, mse_out_max);
      end

      mse_in_valid = 0;  // Disable input MSE valid signal
    end

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule