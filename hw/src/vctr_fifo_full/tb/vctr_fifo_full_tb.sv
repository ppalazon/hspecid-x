`timescale 1ns / 1ps

import hsid_pkg::*;

module vctr_fifo_full_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,
    parameter HSP_BANDS_WIDTH = 3  // 8 entries by default
  );

  localparam int VECTOR_LENGTH = 2 ** HSP_BANDS_WIDTH; // Length of the vector for testbench

  reg clk;
  reg rst_n;
  reg data_in_en;
  reg [WORD_WIDTH-1:0] data_in;
  reg data_out_en;
  wire [WORD_WIDTH-1:0] data_out;
  reg start;
  wire done;
  wire idle;
  wire ready;

// Generate 2 simple vectors with 8 values each
  reg [WORD_WIDTH-1:0] vctr_sum [];

  vctr_fifo_full #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_en(data_in_en),
    .data_in(data_in),
    .data_out_en(data_out_en),
    .data_out(data_out),
    .start(start),
    .done(done),
    .idle(idle),
    .ready(ready)
  );

// Random class to generate test vectors
  VctrFifoFullGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH)
  ) vffg;

// Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, vctr_fifo_full_tb);
  end

  initial begin
    clk = 0;
    rst_n = 1;
    data_in_en = 0;
    data_in = 0;
    data_out_en = 0;
    start = 0;

    // Reset the DUT
    #10;
    rst_n = 0;
    #10;
    rst_n = 1; // Release reset

    // Initialize vectors
    vffg = new();
    for (int i = 0; i < 10; i++) begin
      if (!vffg.randomize()) $fatal(0, "Failed to randomize vectors");

      vffg.sum_vctr(vctr_sum);

      $display("Vector 1: %p", vffg.vctr1);
      $display("Vector 2: %p", vffg.vctr2);
      $display("Expected sum: %p", vctr_sum);

      $display("Test case 1: Start operation");
      start = 1;
      #10;
      if(!ready) begin
        $error("Error: DUT not ready to start operation");
        $finish;
      end

      start = 0; // Clear start signal
      #10;
      $display("Loading vectors into DUT...");

      // Load first vector
      data_in_en = 1;
      for (int i = 0; i < VECTOR_LENGTH; i++) begin
        data_in = vffg.vctr1[i];
        #10;
      end
      // #10; // Wait a bit before loading the second vector
      // Load second vector
      for (int i = 0; i < VECTOR_LENGTH; i++) begin
        data_in = vffg.vctr2[i];
        #10;
      end
      data_in_en = 0; // Disable input data

      // Wait for operation to complete
      while (!done) begin
        #10;
      end
      $display("Operation done, reading output...");
      data_out_en = 1; // Enable output reading
      for (int i = 0; i < VECTOR_LENGTH; i++) begin
        #10;
        // $display("Element [%0d], Vector1: %d, Vector2: %d, Results: %d", i, vffg.vctr1[i], vffg.vctr2[i], data_out);
        if (data_out !== vctr_sum[i]) begin
          $error("Error: Output data does not match expected value. Expected: %h, Got: %h", vctr_sum[i], data_out);
        end
      end

      data_out_en = 0; // Disable output reading
      $display("Test case completed successfully");
      #10;

      if (!idle) begin
        $error("Error: DUT not idle after operation");
      end

    end

    // End simulation
    $display("Testbench completed");
    $finish;
  end

  always
    #5 clk = ! clk;

endmodule

