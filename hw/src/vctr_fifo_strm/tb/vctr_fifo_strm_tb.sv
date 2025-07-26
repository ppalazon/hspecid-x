`timescale 1ns / 1ps

import hsid_pkg::*;

module vctr_fifo_strm_tb;

  localparam int DATA_WIDTH = HSID_DATA_WIDTH;
  localparam int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH;
  localparam int BUFFER_WIDTH = 2;

  localparam int HSP_BANDS = 2 ** HSP_BANDS_WIDTH; // Length of the vector for testbench

  reg clk;
  reg rst_n;
  reg data_in_v1_en;
  reg [DATA_WIDTH-1:0] data_in_v1;
  reg data_in_v2_en;
  reg [DATA_WIDTH-1:0] data_in_v2;
  reg data_out_en;
  wire [DATA_WIDTH-1:0] data_out;
  wire data_out_empty;
  reg [HSP_BANDS_WIDTH-1:0] vector_length;
  reg start;
  wire done;
  wire idle;
  wire ready;

  vctr_fifo_strm #(
    .DATA_WIDTH(DATA_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .BUFFER_WIDTH(BUFFER_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_v1_en(data_in_v1_en),
    .data_in_v1(data_in_v1),
    .data_in_v1_full(),
    .data_in_v2_en(data_in_v2_en),
    .data_in_v2(data_in_v2),
    .data_in_v2_full(),
    .data_out_en(data_out_en),
    .data_out(data_out),
    .data_out_empty(data_out_empty),
    .vector_length(vector_length),
    .start(start),
    .done(done),
    .idle(idle),
    .ready(ready)
  );

  // Generate 2 simple vectors with 8 values each
  reg [DATA_WIDTH-1:0] vctr_1 [0:HSP_BANDS-1];
  reg [DATA_WIDTH-1:0] vctr_2 [0:HSP_BANDS-1];
  reg [DATA_WIDTH-1:0] vctr_sum [0:HSP_BANDS-1];

  // Count inserted and processed elements
  integer processed = 0;
  integer inserted = 0;

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, vctr_fifo_strm_tb);
  end

  initial begin
    clk = 1;
    rst_n = 0;
    data_in_v1_en = 0;
    data_in_v1 = 0;
    data_in_v2_en = 0;
    data_in_v2 = 0;
    data_out_en = 0;
    vector_length = HSP_BANDS[HSP_BANDS_WIDTH-1:0]; // 8 elements
    start = 0;

    // Initialize test vectors
    for (int i=0; i<HSP_BANDS; i++) begin
      vctr_1[i] = 16'h0001 + i; // 0x0001, 0x0002, ..., 0x0008
      vctr_2[i] = HSP_BANDS + 1 + i; // 0x0009, 0x000A, ..., 0x0010
      vctr_sum[i] = vctr_1[i] + vctr_2[i]; // Expected sum
    end

    // Release reset
    #10;
    rst_n = 1;
    #10;

    // Start the operation
    $display("Test case 1: Start operation");
    start = 1;
    #10;
    if(!ready) begin
      $error("Error: DUT not ready to start operation");
      $finish;
    end
    start = !ready; // Clear start signal

    $display("Test case 2: Inserting vectors into DUT...");
    // Load vector length
    data_in_v1_en = 1;
    data_in_v2_en = 1;

    // COMPUTE state
    while (!done) begin
      // Insert elements into the DUT
      if (inserted < vector_length) begin
        // Load first vector
        data_in_v1_en = 1;
        data_in_v2_en = 1;
        data_in_v1 = vctr_1[inserted];
        data_in_v2 = vctr_2[inserted];
        inserted++;
      end else begin
        data_in_v1_en = 0; // Disable input when all elements are inserted
        data_in_v2_en = 0;
      end

      // Read data from DUT if available
      if (!data_out_empty) begin
        data_out_en = 1;
      end else begin
        data_out_en = 0;
      end

      // Wait for a clock cycle to write and read data
      #10;

      if (data_out_en) begin
        $display("Processed element on the fly %0d: %h", processed, data_out);
        if (data_out !== vctr_sum[processed]) begin
          $error("Error: Output mismatch at index %0d: expected %h, got %h", processed, vctr_sum[processed], data_out);
          $finish;
        end
        processed++;
      end
    end

    // DONE state
    while (done) begin
      // Read remaining data from DUT
      if (!data_out_empty) begin
        data_out_en = 1;
      end else begin
        data_out_en = 0;
      end

      #10;

      if (data_out_en) begin
        $display("Processed element after done %0d: %h", processed, data_out);
        if (data_out !== vctr_sum[processed]) begin
          $error("Error: Output mismatch at index %0d: expected %h, got %h", processed, vctr_sum[processed], data_out);
          $finish;
        end
        processed++;
      end
    end

    #10;
    $display("Test case completed successfully");

    if (!idle) begin
      $error("Error: DUT not idle after operation");
    end

    $finish;

  end

  always
    #5 clk = ! clk;

endmodule