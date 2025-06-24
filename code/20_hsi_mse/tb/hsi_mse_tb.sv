`timescale 1ns / 1ps

import hsi_mse_pkg::*;

module hsi_mse_tb;

  localparam WORD_WIDTH = HM_WORD_WIDTH; // Width of the word in bits
  localparam DATA_WIDTH = HM_DATA_WIDTH; // 16 bits by default
  localparam DATA_WIDTH_MUL = HM_DATA_WIDTH_MUL; // Data width for multiplication, larger than WORD_WIDTH
  localparam DATA_WIDTH_ACC = HM_DATA_WIDTH_ACC; // Data width for accumulator, larger than WORD_WIDTH
  localparam HSI_BANDS = HM_HSI_BANDS; // Number of HSI bands
  localparam DATA_PER_WORD = WORD_WIDTH / DATA_WIDTH; // Number of data elements per word
  localparam ELEMENTS = HSI_BANDS / DATA_PER_WORD; // Number of elements in the vector

  reg clk;
  reg rst_n;
  reg start_vctr;
  reg [WORD_WIDTH-1:0] element_a;
  reg [WORD_WIDTH-1:0] element_b;
  reg element_valid;
  wire [WORD_WIDTH-1:0] mse;
  wire mse_valid;

  hsi_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_BANDS(HSI_BANDS)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .start_vctr(start_vctr),
    .element_a(element_a),
    .element_b(element_b),
    .element_valid(element_valid),
    .mse(mse),
    .mse_valid(mse_valid)
  );

  // Test vectors
  logic [WORD_WIDTH-1:0] vctr1 [ELEMENTS];
  logic [WORD_WIDTH-1:0] vctr2 [ELEMENTS];
  logic [WORD_WIDTH-1:0] expected_mse;

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsi_mse_tb);
  end

  HsiMseGen hsi_mse_gen = new();

  initial begin
    clk = 1;
    rst_n = 1;
    start_vctr = 0;
    element_a = 0;
    element_b = 0;
    element_valid = 0;

    #10 rst_n = 0;  // Reset the DUT
    #10 rst_n = 1;  // Release reset

    for (int i=0; i<3; i++) begin
      // Generate random vectors
      if (hsi_mse_gen.randomize()) begin
        hsi_mse_gen.fusion_vctr(vctr1, vctr2);
        hsi_mse_gen.mse(expected_mse);

        // Start processing the vectors
        element_valid = 1;

        for (int j = 0; j < ELEMENTS; j++) begin
          if (j == 0) begin
            start_vctr = 1; // Start the vector processing
          end else begin
            start_vctr = 0;
          end
          element_a = vctr1[j];
          element_b = vctr2[j];
          #10; // Wait for a clock cycle
        end

        // element_valid = 0;

        // Wait for the MSE to be valid
        wait(mse_valid);
        if (mse == expected_mse) begin
          $display("Test %0d: MSE is correct: %0d", i, mse);
        end else begin
          $display("Test %0d: MSE is incorrect: expected %0d, got %0d", i, expected_mse, mse);
        end
        #10; // Wait for a clock cycle before the next test
      end else begin
        $display("Failed to randomize vectors");
      end
    end

    #60; // Wait for the last MSE calculation to complete

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule