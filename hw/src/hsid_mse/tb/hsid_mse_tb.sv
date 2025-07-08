`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_mse_tb;

  localparam WORD_WIDTH = HSID_WORD_WIDTH; // Width of the word in bits
  localparam DATA_WIDTH = HSID_DATA_WIDTH; // 16 bits by default
  localparam DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL; // Data width for multiplication, larger than WORD_WIDTH
  localparam DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC; // Data width for accumulator, larger than WORD_WIDTH
  localparam HSI_BANDS = HSID_MAX_HSP_BANDS; // Number of HSI bands
  localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS); // Address width for HSI bands
  localparam DATA_PER_WORD = WORD_WIDTH / DATA_WIDTH; // Number of data elements per word
  localparam ELEMENTS = HSI_BANDS / DATA_PER_WORD; // Number of elements in the vector
  localparam HSI_LIBRARY_SIZE = HSID_MAX_HSP_LIBRARY; // Size of the HSI library
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);

  reg clk;
  reg rst_n;
  reg element_start;
  reg element_last;
  reg [WORD_WIDTH-1:0] element_a;
  reg [WORD_WIDTH-1:0] element_b;
  reg element_valid;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] vctr_ref; // Reference vector for MSE
  reg [HSI_BANDS_ADDR:0] hsi_bands; // HSI bands to process
  wire [WORD_WIDTH-1:0] mse_value;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] mse_ref; // Reference vector for MSE
  wire mse_valid;

  hsid_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_BANDS(HSI_BANDS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .element_start(element_start),
    .element_last(element_last),
    .vctr_ref(vctr_ref),
    .element_a(element_a),
    .element_b(element_b),
    .element_valid(element_valid),
    .hsi_bands(hsi_bands),
    .mse_value(mse_value),
    .mse_ref(mse_ref),
    .mse_valid(mse_valid)
  );

  // Test vectors
  logic [WORD_WIDTH-1:0] vctr1 [ELEMENTS];
  logic [WORD_WIDTH-1:0] vctr2 [ELEMENTS];
  logic [WORD_WIDTH-1:0] expected_mse [ELEMENTS];
  logic [WORD_WIDTH-1:0] acc_in [HSI_LIBRARY_SIZE][HSI_BANDS];

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_mse_tb);
  end

  HsidMseGen hsi_mse_gen = new();

  initial begin
    clk = 1;
    rst_n = 1;
    element_start = 0;
    element_last = 0; // Not used in this test, but required by the DUT
    element_a = 0;
    element_b = 0;
    element_valid = 0;
    vctr_ref = 0;
    hsi_bands = HSI_BANDS; // Set the number of HSI bands to process

    #5 rst_n = 0;  // Reset the DUT
    #5 rst_n = 1;  // Release reset

    for (int i=0; i<3; i++) begin
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
        element_valid = 1;
        vctr_ref = (i+1) % HSI_LIBRARY_SIZE; // Set the reference vector for MSE

        for (int j = 0; j < ELEMENTS; j++) begin
          if (j == 0) begin
            element_start = 1; // Start the vector processing
          end else begin
            element_start = 0;
          end
          if (j == ELEMENTS - 1) begin
            element_last = 1;
          end else begin
            element_last = 0;
          end
          element_a = vctr1[j];
          element_b = vctr2[j];
          #10; // Wait for a clock cycle
        end
        element_valid = 0;
      end else begin
        $display("Failed to randomize vectors");
      end
    end

    #60; // Wait for the last MSE calculation to complete

    $finish;
  end

  int mse_order = 0;
  always @(posedge mse_valid) begin
    assert (mse_value == expected_mse[mse_order]) begin
      $display("Test %0d: MSE is correct: %0d", mse_order, mse_value);
    end else begin
      $display("Test %0d: MSE is incorrect: expected %0d, got %0d", mse_order, expected_mse[mse_order], mse_value);
    end
    assert (mse_ref == (mse_order +1)) begin
      $display("Test %0d: Reference vector is correct: %0d", mse_order, mse_ref);
    end else begin
      $display("Test %0d: Reference vector is incorrect: expected %0d, got %0d", mse_order, (mse_order + 1), mse_ref);
    end
    mse_order++;
  end

  always
    #5 clk = ! clk;

endmodule