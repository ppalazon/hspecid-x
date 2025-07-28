`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_mse_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // Data width for HSP bands
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than WORD_WIDTH
    parameter TEST_BANDS = HSID_TEST_BANDS, // Number of HSP bands to test
    parameter TEST_LIBRARY_SIZE = HSID_TEST_LIBRARY_SIZE, // Size of the HSI library to test
    parameter TEST_RND_INSERT = 1 // Enable random insertion of test vectors
  );

  parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH; // Address width for HSP bands
  parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH;
  localparam TEST_BAND_PACKS = TEST_BANDS / 2; // Number of band packs in the vector for testbe

  reg clk;
  reg rst_n;
  reg clear;  // Clear signal to reset MSE values
  reg band_pack_start;
  reg band_pack_last;
  reg [WORD_WIDTH-1:0] band_pack_a;
  reg [WORD_WIDTH-1:0] band_pack_b;
  reg band_pack_valid;
  reg [HSP_LIBRARY_WIDTH-1:0] vctr_ref; // Reference vector for MSE
  reg [HSP_BANDS_WIDTH-1:0] hsi_bands; // HSP bands to process
  wire [WORD_WIDTH-1:0] mse_value;
  wire [HSP_LIBRARY_WIDTH-1:0] mse_ref; // Reference vector for MSE
  wire mse_valid;
  wire mse_of; // Overflow flag for mean square error

  hsid_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .clear(clear),
    .band_pack_start(band_pack_start),
    .band_pack_last(band_pack_last),
    .vctr_ref(vctr_ref),
    .band_pack_a(band_pack_a),
    .band_pack_b(band_pack_b),
    .band_pack_valid(band_pack_valid),
    .hsi_bands(hsi_bands),
    .mse_value(mse_value),
    .mse_ref(mse_ref),
    .mse_valid(mse_valid),
    .mse_of(mse_of)
  );

  // Test vectors
  logic [WORD_WIDTH-1:0] vctr1 [TEST_BAND_PACKS];
  logic [WORD_WIDTH-1:0] vctr2 [TEST_BAND_PACKS];
  logic [WORD_WIDTH-1:0] expected_mse [TEST_LIBRARY_SIZE];
  logic [WORD_WIDTH-1:0] acc_in [TEST_LIBRARY_SIZE][TEST_BANDS];

  // Random value
  int count_insert = 0;

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_mse_tb);
  end

  HsidMseGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .TEST_BANDS(TEST_BANDS),
    .TEST_LIBRARY_SIZE(TEST_LIBRARY_SIZE),
    .TEST_BAND_PACKS(TEST_BAND_PACKS)
  ) hsi_mse_gen= new();

  initial begin
    clk = 1;
    rst_n = 1;
    clear = 0;
    band_pack_start = 0;
    band_pack_last = 0; // Not used in this test, but required by the DUT
    band_pack_a = 0;
    band_pack_b = 0;
    band_pack_valid = 0;
    vctr_ref = 0;
    hsi_bands = TEST_BANDS; // Set the number of HSP bands to process

    #5 rst_n = 0;  // Reset the DUT
    #5 rst_n = 1;  // Release reset

    for (int i=0; i<TEST_LIBRARY_SIZE; i++) begin
      // Generate random vectors
      if (hsi_mse_gen.randomize()) begin
        hsi_mse_gen.fusion_vctr(vctr1, vctr2);
        hsi_mse_gen.mse(expected_mse[i]);
        hsi_mse_gen.acc_all(acc_in[i]);

        $display("Test %0d: Vctr1: %p", i, hsi_mse_gen.vctr1);
        $display("Test %0d: Vctr2: %p, ", i, hsi_mse_gen.vctr2);
        $display("Test %0d: Expected MSE: %0d", i, expected_mse[i]);
        $display("Test %0d: Accumulated: %p", i, acc_in[i]);

        // Start processing the vectors

        vctr_ref = i[TEST_LIBRARY_SIZE-1:0]+1; // Set the reference vector for MSE

        count_insert = 0;
        while (count_insert < TEST_BAND_PACKS) begin
          band_pack_valid = TEST_RND_INSERT ? $urandom % 2: 1; // Randomly enable or disable element processing
          if (count_insert == 0) begin
            band_pack_start = 1; // Start the vector processing
          end else begin
            band_pack_start = 0;
          end
          if (count_insert == TEST_BAND_PACKS - 1) begin
            band_pack_last = 1;
          end else begin
            band_pack_last = 0;
          end
          band_pack_a = vctr1[count_insert];
          band_pack_b = vctr2[count_insert];
          #10; // Wait for a clock cycle
          if (band_pack_valid) count_insert++;
        end
        band_pack_valid = 0;
      end else begin
        $display("Failed to randomize vectors");
      end
    end

    $display("Expected MSE values: %p", expected_mse);

    #100; // Wait for the last MSE calculation to complete

    $finish;
  end

  int mse_order = 0;
  always @(posedge mse_valid) begin
    assert (mse_value == expected_mse[mse_order]) begin
      $display("Test %0d: MSE is correct: %0d", mse_order, mse_value);
    end else begin
      $error("Test %0d: MSE is incorrect: expected %0d, got %0d", mse_order, expected_mse[mse_order], mse_value);
    end
    assert (mse_ref == (mse_order +1)) begin
      $display("Test %0d: Reference vector is correct: %0d", mse_order, mse_ref);
    end else begin
      $error("Test %0d: Reference vector is incorrect: expected %0d, got %0d", mse_order, (mse_order + 1), mse_ref);
    end
    mse_order++;
  end

  always
    #5 clk = ! clk;

endmodule