`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_fifo_tb;

  // Parameters
  parameter DATA_WIDTH = 8;
  parameter FIFO_DEPTH = 16;
  parameter FIFO_ALMOST_FULL_THRESHOLD = FIFO_DEPTH - 2; // Optional threshold for almost full

  // Signals
  reg clk;
  reg rst_n;
  reg wr_en;
  reg rd_en;
  reg [DATA_WIDTH-1:0] write_data;
  wire [DATA_WIDTH-1:0] read_data;
  wire full;
  wire almost_full;
  wire empty;

  // Instantiate the FIFO module
  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(FIFO_DEPTH)
  ) uut (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .data_in(write_data),
    .data_out(read_data),
    .full(full),
    .almost_full(almost_full),
    .empty(empty)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");     // Name of VCD file
    $dumpvars(0, hsid_fifo_tb);   // Replace 'testbench' with your top module name
  end

  // Testbench logic
  initial begin
    // Initialize signals
    clk = 0;
    rst_n = 1;
    wr_en = 0;
    rd_en = 0;
    write_data = 0;

    // Reset the FIFO
    #10 rst_n = 0;
    #10 rst_n = 1;

    // Test case 0: Write and read
    $display("Test case 0: Write and read");
    wr_en = 1;
    write_data = 8'hA;
    #10;
    wr_en = 0;
    rd_en = 1;
    #10;
    if (read_data !== 8'ha)
      $error("Error reading value %h", read_data);
    // else $display("Reading value: %h", read_data);

    // Reset values
    write_data = 0;
    wr_en = 0;
    rd_en = 0;

    // Test case 1: Write 16 values and check it's full
    for (int i=0; i<FIFO_DEPTH; i++) begin
      // Empty check
      if (i==0) begin
        if (!empty) $error("Error: FIFO should be empty but it is not.");
      end else begin
        if (empty) $error("Error: FIFO should not be empty but it is.");
      end
      write_data = i[DATA_WIDTH-1:0]; // Truncate to DATA_WIDTH bits
      wr_en = 1;
      #10;
      if(i >= FIFO_ALMOST_FULL_THRESHOLD) begin
        if (!almost_full) $error("Error: FIFO should be almost full but it is not.");
      end else begin
        if (almost_full) $error("FIFO is almost full when it should not be.");
      end
    end
    if (!full) $error("Error setting full variable after writing 32 values");

    // Test case 2: Write on full
    $display("Test Case 2: Write on full");
    wr_en = 1;
    write_data = 20;
    #10;
    wr_en = 0;

    // Test case 3: Read until empty
    $display("Test Case 3: Read until empty");
    for (int i=0; i<FIFO_DEPTH; i++) begin
      // Full check
      if (i==0) begin
        if (!full) $error("Error: FIFO should be full but it is not.");
      end else begin
        if (full) $error("Error: FIFO should not be full but it is.");
      end
      // Almost full check
      if(i >= 2) begin
        if (almost_full) $error("Error: FIFO should not be almost full but it is.");
      end else begin
        if (!almost_full) $error("FIFO is not almost full as expected");
      end
      rd_en = 1;
      #10;
      if (read_data !== i[DATA_WIDTH-1:0]) begin
        $error("Error: Read data does not match expected data!. Read data: %d , expected: %d", read_data, i[DATA_WIDTH-1:0]);
      end
    end
    if (!empty) $error("Error setting empty after reading all values");
    rd_en = 0;

    // Test case 4: Read on empty
    $display("Test Case 4: Read on empty");
    rd_en = 1;
    #10;
    if (!empty) begin
      $error("Error: FIFO should be empty but it is not.");
    end
    if (read_data !== FIFO_DEPTH-1) begin
      $error("Error: Read data should be %d but it is %d", FIFO_DEPTH-1, read_data);
    end
    rd_en = 0;

    // Test case 5: Write and read in the same cycle
    $display("Test Case 5: Write and read in the same cycle");
    wr_en = 1;
    rd_en = 1;
    // TODO: Possibility of write-through FIFO??
    // Write and read 5 values at the same time, it would be a delay of one clock cycle
    write_data = 8'h10; // Last read values is 8'h0F, so we start writing from 8'h10
    for (int i=0; i<5; i++) begin
      #10;
      if (read_data !== write_data-1) begin // 15/16, 16/17, 17/18, 18/19, 19/20
        $error("Error: Read data does not match written data. Read data: %d, Written data: %d", read_data, write_data);
      end
      write_data = write_data + 1;
    end
    wr_en = 0;
    rd_en = 0;

    // End simulation
    $display("Testbench completed");
    $finish;
  end

endmodule

