`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_main_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than DATA_WIDTH
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSI_BANDS = HSID_MAX_HSP_BANDS,  // Number of HSI bands
    parameter BUFFER_LENGTH = HSID_BUFFER_LENGTH,  // Length of the buffer
    parameter HSI_LIBRARY_SIZE = HSID_MAX_HSP_LIBRARY,  // Size of the HSI library
    parameter TEST_BANDS = HSID_TEST_BANDS, // Number of HSI bands to test
    parameter TEST_LIBRARY_SIZE = HSID_TEST_LIBRARY_SIZE, // Size of the HSI library to test
    parameter TEST_RND_INSERT = 1 // Enable random insertion of test vectors
  ) ();

  localparam ELEMENTS = HSI_BANDS / 2;  // Number of elements in the vector
  localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS);  // Address width for HSI bands
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);
  localparam TEST_ELEMENTS = TEST_BANDS / 2; // Number of elements in the vector for testbench

  reg clk;
  reg rst_n;
  reg hsi_vctr_in_valid;
  reg [WORD_WIDTH-1:0] hsi_vctr_in;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] library_size_in;
  reg [HSI_BANDS_ADDR-1:0] hsi_bands_in;  // HSI bands to process
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref;
  wire [WORD_WIDTH-1:0] mse_min_value;
  wire [WORD_WIDTH-1:0] mse_max_value;

  // Block interface for handshake signals
  reg start;
  reg clear;  // Clear signal to reset MSE values
  wire done;
  wire idle;
  wire ready;

  hsid_main #(
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
    .hsi_bands_in(hsi_bands_in),
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

  HsidMainGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),  // Data width for multiplication, larger than DATA_WIDTH
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),  // Data width for accumulator, larger than DATA_WIDTH
    .TEST_BANDS(TEST_BANDS),
    .TEST_LIBRARY_SIZE(TEST_LIBRARY_SIZE)
  ) hsid_main_gen = new();

  // Test vectors
  logic [DATA_WIDTH-1:0] captured [TEST_BANDS];
  logic [DATA_WIDTH-1:0] lib [TEST_LIBRARY_SIZE][TEST_BANDS];
  logic [WORD_WIDTH-1:0] acc_in [TEST_LIBRARY_SIZE][TEST_BANDS];
  logic [WORD_WIDTH-1:0] expected_mse [TEST_LIBRARY_SIZE];

  logic [WORD_WIDTH-1:0] min_mse_value_expected;
  logic [WORD_WIDTH-1:0] max_mse_value_expected;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] min_mse_ref_expected;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] max_mse_ref_expected;

  logic [WORD_WIDTH-1:0] fusion_vctr [TEST_ELEMENTS];

  // Count for the number of inserted elements
  int count_insert;
  logic insert_en;

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_main_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    hsi_vctr_in_valid = 0;
    hsi_vctr_in = 0;
    library_size_in = 0;
    start = 0;
    clear = 0;
    hsi_bands_in = TEST_BANDS;  // Set HSI bands to maximum
    library_size_in = TEST_LIBRARY_SIZE;  // Set library size to maximum

    // Generate a random vector as a measure
    if (hsid_main_gen.randomize()) begin : randomize_measure
      captured = hsid_main_gen.measure;
    end

    $display("Captured vector: %p", captured[0:TEST_BANDS-1]);

    // Generate random library vectors
    for (int i = 0; i < TEST_LIBRARY_SIZE; i++) begin : generate_library
      if (hsid_main_gen.randomize()) begin
        lib[i] = hsid_main_gen.measure;
        hsid_main_gen.mse(captured, lib[i], expected_mse[i]);
        hsid_main_gen.acc_all(captured, lib[i], acc_in[i]);
        $display("Library vector %0d: %p, MSE: %d", i, lib[i][0:TEST_BANDS-1], expected_mse[i]);
        $display("Accumulated %0d:    %p,", i, acc_in[i][0:TEST_BANDS-1]);
      end
    end

    // Compute expected min and max MSE values and references
    hsid_main_gen.min_max_mse(expected_mse,
      min_mse_value_expected, max_mse_value_expected,
      min_mse_ref_expected, max_mse_ref_expected);

    $display("Expected min MSE: %0d, ref: %0d", min_mse_value_expected, min_mse_ref_expected);
    $display("Expected max MSE: %0d, ref: %0d", max_mse_value_expected, max_mse_ref_expected);

    // Reset the DUT
    #3 rst_n = 0;
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
    hsid_main_gen.fusion_vctr(captured, fusion_vctr);
    count_insert = 0;
    while (count_insert < TEST_ELEMENTS) begin
      insert_en = TEST_RND_INSERT ? $urandom % 2 : 1; // Randomly enable or disable element processing
      hsi_vctr_in = fusion_vctr[count_insert];
      hsi_vctr_in_valid = insert_en;
      #10;
      assert (ready == 1) else $fatal(0, "DUT is not ready to accept input");
      if (insert_en) count_insert++;
    end

    hsi_vctr_in_valid = 0;  // Disable input vector valid signal
    hsi_vctr_in = 0;  // Reset input vector

    #10;
    $display("Sending library vectors...");

    // Send the library vectors
    for (int i = 0; i < TEST_LIBRARY_SIZE; i++) begin
      hsid_main_gen.fusion_vctr(lib[i], fusion_vctr);
      count_insert = 0;
      for (int j = 0; j < TEST_ELEMENTS; j++) begin
        insert_en = TEST_RND_INSERT ? $urandom % 2 : 1; // Randomly enable or disable element processing
        hsi_vctr_in = fusion_vctr[j];
        hsi_vctr_in_valid = insert_en;
        #10;
        if (!(i == TEST_LIBRARY_SIZE - 1 && j == TEST_ELEMENTS - 1)) begin
          assert (ready == 1) else $fatal(0, "DUT is not ready to accept input");
        end
        if (insert_en) count_insert++;
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

  initial begin
    #1000; $finish;  // Timeout to prevent infinite simulation
  end

  always
    #5 clk = ! clk;

endmodule