`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_mse_comp_tb;

  localparam WORD_WIDTH = HSID_WORD_WIDTH;  // Width of the word in bits
  localparam HSI_LIBRARY_SIZE = HSID_MAX_HSP_LIBRARY;  // Size of the HSI library
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);

  reg clk;
  reg rst_n;
  reg mse_in_valid;
  reg [WORD_WIDTH-1:0] mse_in;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] mse_in_ref;  // Reference value for MSE, initialized to 0
  reg clear;  // Clear signal, not used in this test
  wire mse_out_valid;
  wire mse_min_changed;
  wire mse_max_changed;
  wire [WORD_WIDTH-1:0] mse_min_value;
  wire [WORD_WIDTH-1:0] mse_max_value;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref;

  // Aux min and max values for comparison
  logic [WORD_WIDTH-1:0] aux_min_value = 32'hFFFFFFFF;  // Initialize aux_min to max value
  logic [WORD_WIDTH-1:0] aux_max_value = 32'h0;  // Initialize aux_max to min value
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] aux_min_ref = 0; // Initialize aux_min_ref to 0
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] aux_max_ref = 0; // Initialize aux_max_ref to 0
  logic aux_min_changed = 0;  // Initialize aux_min_changed to 0
  logic aux_max_changed = 0;  // Initialize aux_max_changed to 0


  hsid_mse_comp #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .mse_in_valid(mse_in_valid),
    .mse_out_valid(mse_out_valid),
    .mse_in_value(mse_in),
    .mse_in_ref(mse_in_ref),
    .clear(clear),
    .mse_min_value(mse_min_value),
    .mse_min_ref(mse_min_ref),
    .mse_min_changed(mse_min_changed),
    .mse_max_value(mse_max_value),
    .mse_max_ref(mse_max_ref),
    .mse_max_changed(mse_max_changed)
  );

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_mse_comp_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    mse_in_valid = 0;
    mse_in = 0;
    mse_in_ref = 0;
    clear = 0;

    #10 rst_n = 0;  // Reset the DUT
    #10 rst_n = 1;  // Release reset

    // First value: medium
    mse_in_valid = 1;
    mse_in = 32'h0000FFFF;  // Input MSE value
    mse_in_ref = 12'h1;
    #10;
    mse_in_valid = 0;  // Disable input MSE valid signal

    if (mse_out_valid && mse_min_value == 32'h0000FFFF && mse_max_value == 32'h0000FFFF) begin
      $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    end else begin
      $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    end

    // Second value: bigger
    mse_in_valid = 1;
    mse_in = 32'h000FFFFF;  // Input MSE value
    mse_in_ref = 12'h2;
    #10;
    mse_in_valid = 0;  // Disable input MSE valid signal

    if (mse_out_valid && mse_min_value == 32'h0000FFFF && mse_max_value == 32'h000FFFFF) begin
      $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    end else begin
      $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    end

    // Second value: smaller
    mse_in_valid = 1;
    mse_in = 32'h00000FFF;  // Input MSE value
    mse_in_ref = 12'h3;
    #10;
    mse_in_valid = 0;  // Disable input MSE valid signal

    if (mse_out_valid && mse_min_value == 32'h00000FFF && mse_max_value == 32'h000FFFFF) begin
      $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    end else begin
      $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    end

    // Clear the output
    clear = 1;
    #10;
    clear = 0;
    #10;

    assert (mse_out_valid == 0) else $error("Output MSE valid signal should be low after clear");
    assert (mse_min_value == 32'hFFFFFFFF) else $error("Output MSE min value should be reset to max value");
    assert (mse_max_value == 32'h0) else $error("Output MSE max value should be reset to min value");
    assert (mse_min_ref == 0) else $error("Output MSE min reference should be reset to 0");
    assert (mse_max_ref == 0) else $error("Output MSE max reference should be reset to 0");
    assert (mse_min_changed == 0) else $error("Output MSE min changed flag should be reset to 0");

    for (int i = 0; i < 50; i++) begin
      mse_in_valid = $urandom % 2;
      mse_in = $urandom;  // Random MSE value
      mse_in_ref = i % HSI_LIBRARY_SIZE;  // Random reference value within library size
      if (mse_in_valid) begin
        aux_min_changed = mse_in <= aux_min_value;
        aux_max_changed = mse_in >= aux_max_value;
        aux_min_value = (aux_min_changed) ? mse_in : aux_min_value;  // Update aux_min
        aux_max_value = (aux_max_changed) ? mse_in : aux_max_value;
        aux_min_ref = (aux_min_changed) ? mse_in_ref : aux_min_ref;  // Update aux_min_ref
        aux_max_ref = (aux_max_changed) ? mse_in_ref : aux_max_ref;  // Update aux_max_ref
      end else begin
        aux_min_changed = 0;  // Reset aux_min_changed
        aux_max_changed = 0;  // Reset aux_max_changed
      end
      #10;

      if (mse_out_valid == mse_in_valid && mse_min_value == aux_min_value && mse_max_value == aux_max_value
          && mse_min_ref == aux_min_ref && mse_max_ref == aux_max_ref
          && mse_max_changed == aux_max_changed && mse_min_changed == aux_min_changed) begin
        $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
      end else begin
        $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
      end

      mse_in_valid = 0;  // Disable input MSE valid signal
    end

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule