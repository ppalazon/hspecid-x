`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than DATA_WIDTH
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSI_BANDS = HSID_HSI_BANDS,  // Number of HSI bands
    parameter BUFFER_LENGTH = HSID_BUFFER_LENGTH,  // Length of the buffer
    parameter HSI_LIBRARY_SIZE = HSID_HSI_LIBRARY_SIZE  // Size of the HSI library
  ) ();

  localparam ELEMENTS = HSI_BANDS / 2;  // Number of elements in the vector
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);

  reg clk;
  reg rst_n;
  reg hsi_vctr_in_valid;
  reg [WORD_WIDTH-1:0] hsi_vctr_in;
  reg [HSI_LIBRARY_SIZE_ADDR:0] library_size_in;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref;
  wire [WORD_WIDTH-1:0] mse_min_value;
  wire [WORD_WIDTH-1:0] mse_max_value;
  reg start;
  reg clear;  // Clear signal to reset MSE values
  wire done;
  wire idle;
  wire ready;

  hsid #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .HSI_BANDS(HSI_BANDS),
    .BUFFER_LENGTH(BUFFER_LENGTH),
    .ELEMENTS(ELEMENTS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .hsi_vctr_in_valid(hsi_vctr_in_valid),
    .hsi_vctr_in(hsi_vctr_in),
    .library_size_in(library_size_in),
    .mse_min_ref(mse_min_ref),
    .mse_max_ref(mse_max_ref),
    .mse_min_value(mse_min_value),
    .mse_max_value(mse_max_value),
    .clear(clear),
    .start(start),
    .done(done),
    .idle(idle),
    .ready(ready)
  );

  HsidGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),  // Data width for multiplication, larger than DATA_WIDTH
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),  // Data width for accumulator, larger than DATA_WIDTH
    .HSI_BANDS(HSI_BANDS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) hsid_gen = new();

  // Test vectors
  logic signed [DATA_WIDTH-1:0] measure [HSI_BANDS];
  logic signed [DATA_WIDTH-1:0] lib [HSI_LIBRARY_SIZE][HSI_BANDS];
  logic [WORD_WIDTH-1:0] acc_in [HSI_LIBRARY_SIZE][HSI_BANDS];
  logic [WORD_WIDTH-1:0] expected_mse [HSI_LIBRARY_SIZE];

  logic [WORD_WIDTH-1:0] min_mse_value_expected;
  logic [WORD_WIDTH-1:0] max_mse_value_expected;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] min_mse_ref_expected;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] max_mse_ref_expected;

  logic [WORD_WIDTH-1:0] fusion_vctr [ELEMENTS];

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    hsi_vctr_in_valid = 0;
    hsi_vctr_in = 0;
    library_size_in = 0;
    start = 0;
    clear = 0;
    library_size_in = 10;  // Set library size to maximum

    // Generate a random vector as a measure
    if (hsid_gen.randomize()) begin : randomize_measure
      measure = hsid_gen.measure;
    end

    $display("Measure vector:   %p", measure);

    // Generate random library vectors
    for (int i = 0; i < library_size_in; i++) begin : generate_library
      if (hsid_gen.randomize()) begin
        lib[i] = hsid_gen.measure;
        hsid_gen.mse(measure, lib[i], expected_mse[i]);
        hsid_gen.acc_all(measure, lib[i], acc_in[i]);
        $display("Library vector %0d: %p, MSE: %d", i, lib[i], expected_mse[i]);
        $display("Accumulated %0d:    %p,", i, acc_in[i]);
      end
    end

    // Compute expected min and max MSE values and references
    hsid_gen.min_max_mse(expected_mse,
      min_mse_value_expected, max_mse_value_expected,
      min_mse_ref_expected, max_mse_ref_expected);

    $display("Expected min MSE: %0d, ref: %0d", min_mse_value_expected, min_mse_ref_expected);
    $display("Expected max MSE: %0d, ref: %0d", max_mse_value_expected, max_mse_ref_expected);

    // Reset the DUT
    #5 rst_n = 0;
    #5 rst_n = 1;  // Release reset

    // Start the DUT
    assert (idle == 1) else $fatal(0, "DUT is not idle at start");
    assert (done == 0) else $fatal(0, "DUT is done before starting");
    assert (ready == 0) else $fatal(0, "DUT is ready before starting");

    start = 1;

    #10;

    start = 0;

    assert (idle == 0) else $fatal(0, "DUT is idle after starting");
    assert (done == 0) else $fatal(0, "DUT is done after starting");
    assert (ready == 1) else $fatal(0, "DUT is not ready after starting");

    // Send the measure vector
    hsid_gen.fusion_vctr(measure, fusion_vctr);
    for (int i = 0; i < ELEMENTS; i++) begin
      hsi_vctr_in = fusion_vctr[i];
      hsi_vctr_in_valid = 1;
      #10;
      assert (ready == 1) else $fatal(0, "DUT is not ready to accept input");
    end

    hsi_vctr_in_valid = 0;  // Disable input vector valid signal
    hsi_vctr_in = 0;  // Reset input vector

    #10;
    $display("Sending library vectors...");

    // Send the library vectors
    for (int i = 0; i < library_size_in; i++) begin
      hsid_gen.fusion_vctr(lib[i], fusion_vctr);
      for (int j = 0; j < ELEMENTS; j++) begin
        hsi_vctr_in = fusion_vctr[j];
        hsi_vctr_in_valid = 1;
        #10;
        if (!(i == library_size_in - 1 && j == ELEMENTS - 1)) begin
          assert (ready == 1) else $fatal(0, "DUT is not ready to accept input");
        end
      end
    end

    hsi_vctr_in_valid = 0;  // Disable input vector valid signal
    hsi_vctr_in = 0;  // Reset input vector

    wait(done);  // Wait for the DUT to finish processing
    $display("DUT is done processing");

    // Check the results
    assert (mse_min_value == min_mse_value_expected) else
      $error(0, "Minimum MSE value is incorrect: expected %0d, got %0d", min_mse_value_expected, mse_min_value);
    assert (mse_max_value == max_mse_value_expected) else
      $error(0, "Maximum MSE value is incorrect: expected %0d, got %0d", max_mse_value_expected, mse_max_value);
    assert (mse_min_ref == min_mse_ref_expected) else
      $error(0, "Minimum MSE reference is incorrect: expected %0d, got %0d", min_mse_ref_expected, mse_min_ref);
    assert (mse_max_ref == max_mse_ref_expected) else
      $error(0, "Maximum MSE reference is incorrect: expected %0d, got %0d", max_mse_ref_expected, mse_max_ref);

    #20;

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule