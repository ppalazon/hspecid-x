`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_mse_comp_tb #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Number of bits for HSI library size
  );

  localparam MAX_WORD = {WORD_WIDTH{1'b1}}; // Maximum value for data vectors
  localparam MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}}; // Maximum value for HSI library

  reg clk;
  reg rst_n;
  reg mse_in_valid;
  reg mse_in_of;
  reg [WORD_WIDTH-1:0] mse_in;
  reg [HSP_LIBRARY_WIDTH-1:0] mse_in_ref;  // Reference value for MSE, initialized to 0
  reg clear;  // Clear signal, not used in this test
  wire mse_out_valid;
  wire mse_min_changed;
  wire mse_max_changed;
  wire [WORD_WIDTH-1:0] mse_min_value;
  wire [WORD_WIDTH-1:0] mse_max_value;
  wire [HSP_LIBRARY_WIDTH-1:0] mse_min_ref;
  wire [HSP_LIBRARY_WIDTH-1:0] mse_max_ref;

  // Expected values for comparison
  logic [WORD_WIDTH-1:0] exp_min_value = MAX_WORD;  // Initialize aux_min to max value
  logic [WORD_WIDTH-1:0] exp_max_value = 'h0;  // Initialize aux_max to min value
  logic [HSP_LIBRARY_WIDTH-1:0] exp_min_ref = 0; // Initialize aux_min_ref to 0
  logic [HSP_LIBRARY_WIDTH-1:0] exp_max_ref = 0; // Initialize aux_max_ref to 0
  logic exp_min_changed = 0;  // Initialize aux_min_changed to 0
  logic exp_max_changed = 0;  // Initialize aux_max_changed to 0
  logic exp_mse_out_valid = 0;  // Initialize aux_mse_out_valid to 0

  hsid_mse_comp #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
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
    .mse_max_changed(mse_max_changed),
    .mse_in_of(mse_in_of)
  );

  // Constraint random values for MSE input
  HsidMseCompRandom #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) mse_comp_random = new();

  // Coverage with covergroup
  covergroup cg_mse_comp @(posedge clk);
    coverpoint mse_out_valid;
    coverpoint mse_min_value iff (mse_out_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins mid = {[1:MAX_WORD-1]};
    }
    coverpoint mse_max_value iff (mse_out_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins mid = {[1:MAX_WORD-1]};
    }
    coverpoint mse_min_ref iff (mse_out_valid) {
      bins zero = {0};
      bins max = {MAX_HSP_LIBRARY};
      bins mid = {[1:MAX_HSP_LIBRARY-1]};
    }
    coverpoint mse_max_ref iff (mse_out_valid) {
      bins zero = {0};
      bins max = {MAX_HSP_LIBRARY};
      bins mid = {[1:MAX_HSP_LIBRARY-1]};
    }
    coverpoint mse_min_changed iff (mse_out_valid);
    coverpoint mse_max_changed iff (mse_out_valid);
    coverpoint mse_in_valid;
    coverpoint mse_in_of;
    coverpoint clear;
    coverpoint mse_in iff (mse_in_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins mid = {[1:MAX_WORD-1]};
    }
    coverpoint mse_in_ref iff (mse_in_valid) {
      bins zero = {0};
      bins max = {MAX_HSP_LIBRARY};
      bins mid = {[1:MAX_HSP_LIBRARY-1]};
    }

    // Cross coverage
    cg_op_comb: cross mse_in_valid, mse_in_of, clear;
  endgroup

  cg_mse_comp cg_mse_comp_inst = new();

  // Bind SVA assertions
  bind hsid_mse_comp hsid_mse_comp_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_mse_comp_sva_inst (.*);

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

    #3 rst_n = 0;  // Reset the DUT
    #15 rst_n = 1;  // Release reset

    for (int i=0; i<1000; i++) begin
      if (!mse_comp_random.randomize()) $fatal(0, "Randomization failed");
      mse_in_valid = mse_comp_random.mse_in_valid;
      mse_in_of = mse_comp_random.mse_in_of;
      mse_in = mse_comp_random.mse_in_value;
      mse_in_ref = mse_comp_random.mse_in_ref;
      clear = mse_comp_random.clear;

      // Compute expected values based on the random input
      if (clear) begin
        exp_min_value = MAX_WORD;
        exp_max_value = 'h0;
        exp_min_ref = 0;
        exp_max_ref = 0;
        exp_min_changed = 0;
        exp_max_changed = 0;
        exp_mse_out_valid = 0;
      end else begin
        exp_mse_out_valid = mse_in_valid;
        if (mse_in_valid && !mse_in_of) begin
          exp_min_changed = mse_in <= exp_min_value;
          exp_max_changed = mse_in >= exp_max_value;
          exp_min_value = (exp_min_changed) ? mse_in : exp_min_value;  // Update aux_min
          exp_max_value = (exp_max_changed) ? mse_in : exp_max_value;
          exp_min_ref = (exp_min_changed) ? mse_in_ref : exp_min_ref;  // Update aux_min_ref
          exp_max_ref = (exp_max_changed) ? mse_in_ref : exp_max_ref;  // Update aux_max_ref
        end else begin
          exp_min_changed = 0;  // Reset aux_min_changed
          exp_max_changed = 0;  // Reset aux_max_changed
        end
      end

      #10;  // Wait for a clock cycle

      a_mse_out_valid: assert (mse_out_valid == exp_mse_out_valid) else $error("Output MSE valid signal mismatch: expected %0d, got %0d", exp_mse_out_valid, mse_out_valid);
      a_mse_min_value: assert (mse_min_value == exp_min_value) else $error("Output MSE min value mismatch: expected %0h, got %0h", exp_min_value, mse_min_value);
      a_mse_max_value: assert (mse_max_value == exp_max_value) else $error("Output MSE max value mismatch: expected %0h, got %0h", exp_max_value, mse_max_value);
      a_mse_min_ref: assert (mse_min_ref == exp_min_ref) else $error("Output MSE min reference mismatch: expected %0h, got %0h", exp_min_ref, mse_min_ref);
      a_mse_max_ref: assert (mse_max_ref == exp_max_ref) else $error("Output MSE max reference mismatch: expected %0h, got %0h", exp_max_ref, mse_max_ref);
      a_mse_min_changed: assert (mse_min_changed == exp_min_changed) else $error("Output MSE min changed flag mismatch: expected %0d, got %0d", exp_min_changed, mse_min_changed);
      a_mse_max_changed: assert (mse_max_changed == exp_max_changed) else $error("Output MSE max changed flag mismatch: expected %0d, got %0d", exp_max_changed, mse_max_changed);

    end

    // // First value: medium
    // mse_in_valid = 1;
    // mse_in = 32'h0000FFFF;  // Input MSE value
    // mse_in_ref = 'h1;
    // #10;
    // mse_in_valid = 0;  // Disable input MSE valid signal

    // if (mse_out_valid && mse_min_value == 32'h0000FFFF && mse_max_value == 32'h0000FFFF) begin
    //   $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    // end else begin
    //   $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    // end

    // // Second value: bigger
    // mse_in_valid = 1;
    // mse_in = 32'h000FFFFF;  // Input MSE value
    // mse_in_ref = 'h2;
    // #10;
    // mse_in_valid = 0;  // Disable input MSE valid signal

    // if (mse_out_valid && mse_min_value == 32'h0000FFFF && mse_max_value == 32'h000FFFFF) begin
    //   $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    // end else begin
    //   $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    // end

    // // Second value: smaller
    // mse_in_valid = 1;
    // mse_in = 32'h00000FFF;  // Input MSE value
    // mse_in_ref = 'h3;
    // #10;
    // mse_in_valid = 0;  // Disable input MSE valid signal

    // if (mse_out_valid && mse_min_value == 32'h00000FFF && mse_max_value == 32'h000FFFFF) begin
    //   $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    // end else begin
    //   $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    // end

    // // Clear the output
    // clear = 1;
    // #10;
    // clear = 0;
    // #10;

    // assert (mse_out_valid == 0) else $error("Output MSE valid signal should be low after clear");
    // assert (mse_min_value == 32'hFFFFFFFF) else $error("Output MSE min value should be reset to max value");
    // assert (mse_max_value == 32'h0) else $error("Output MSE max value should be reset to min value");
    // assert (mse_min_ref == 0) else $error("Output MSE min reference should be reset to 0");
    // assert (mse_max_ref == 0) else $error("Output MSE max reference should be reset to 0");
    // assert (mse_min_changed == 0) else $error("Output MSE min changed flag should be reset to 0");

    // for (int i = 0; i < 50; i++) begin
    //   mse_in_valid = $urandom % 2;
    //   mse_in = $urandom;  // Random MSE value
    //   mse_in_ref = i[HSP_LIBRARY_WIDTH-1:0];  // Random reference value within library size
    //   if (mse_in_valid) begin
    //     aux_min_changed = mse_in <= aux_min_value;
    //     aux_max_changed = mse_in >= aux_max_value;
    //     aux_min_value = (aux_min_changed) ? mse_in : aux_min_value;  // Update aux_min
    //     aux_max_value = (aux_max_changed) ? mse_in : aux_max_value;
    //     aux_min_ref = (aux_min_changed) ? mse_in_ref : aux_min_ref;  // Update aux_min_ref
    //     aux_max_ref = (aux_max_changed) ? mse_in_ref : aux_max_ref;  // Update aux_max_ref
    //   end else begin
    //     aux_min_changed = 0;  // Reset aux_min_changed
    //     aux_max_changed = 0;  // Reset aux_max_changed
    //   end
    //   #10;

    //   if (mse_out_valid == mse_in_valid && mse_min_value == aux_min_value && mse_max_value == aux_max_value
    //       && mse_min_ref == aux_min_ref && mse_max_ref == aux_max_ref
    //       && mse_max_changed == aux_max_changed && mse_min_changed == aux_min_changed) begin
    //     $display("MSE Comparison Valid: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    //   end else begin
    //     $error("MSE Comparison failed: MSE Min: %h, MSE Max: %h", mse_min_value, mse_max_value);
    //   end

    //   mse_in_valid = 0;  // Disable input MSE valid signal
    // end

    #10;  // Wait for a clock cycle before finishing the test

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule