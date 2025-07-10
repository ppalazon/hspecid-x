`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_fifo_tb;

  // Parameters
  localparam DATA_WIDTH = 32;
  localparam FIFO_DEPTH = 16;
  localparam FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH); // Address width for FIFO depth
  localparam FIFO_ALMOST_FULL_THRESHOLD = 10; // Optional threshold for almost full

  // Signals
  reg clk;
  reg rst_n;
  reg wr_en;
  reg rd_en;
  reg loop_en = 0;
  reg [DATA_WIDTH-1:0] fifo_data_in;
  reg [FIFO_ADDR_WIDTH-1:0] almost_full_threshold = FIFO_ALMOST_FULL_THRESHOLD; // Element to process
  wire [DATA_WIDTH-1:0] fifo_data_out;
  wire full;
  wire almost_full;
  wire empty;
  reg clear;

  // Instantiate the FIFO module
  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(FIFO_DEPTH)
  ) uut (
    .clk(clk),
    .rst_n(rst_n),
    .loop_en(loop_en),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .data_in(fifo_data_in),
    .almost_full_threshold(almost_full_threshold),
    .data_out(fifo_data_out),
    .full(full),
    .almost_full(almost_full),
    .empty(empty),
    .clear(clear)
  );

  logic [DATA_WIDTH-1:0] random_values [0:FIFO_DEPTH-1];

  // Clock generation
  always #5 clk = ~clk;

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");     // Name of VCD file
    $dumpvars(0, hsid_fifo_tb);   // Replace 'testbench' with your top module name
  end

  // Testbench logic
  initial begin
    foreach (random_values[i]) begin
      random_values[i] = $urandom(); // Generate random values between 0 and 255
    end

    // Initialize signals
    clk = 1;
    rst_n = 1;
    wr_en = 0;
    rd_en = 0;
    fifo_data_in = 0;
    clear = 0;
    loop_en = 0;

    // Reset the FIFO
    #10 rst_n = 0;
    #10 rst_n = 1;

    // Test case 0: Write and read
    $display("Test case 0: Write and read");
    wr_en = 1;
    fifo_data_in = 32'hA;
    #10;
    wr_en = 0;
    rd_en = 1;
    #10;
    if (fifo_data_out !== 32'ha)
      $error("Error reading value %h", fifo_data_out);
    // else $display("Reading value: %h", read_data);

    // Reset values
    fifo_data_in = 0;
    wr_en = 0;
    rd_en = 0;

    // Test case 1: Write 16 values and check it's full
    $display("Test case 1: Write 16 values and check it's full");
    for (int i=0; i<FIFO_DEPTH; i++) begin
      // Empty check
      if (i==0) begin
        if (!empty) $error("Error: FIFO should be empty but it is not.");
      end else begin
        if (empty) $error("Error: FIFO should not be empty but it is.");
      end
      fifo_data_in = i[DATA_WIDTH-1:0]; // Truncate to DATA_WIDTH bits
      wr_en = 1;
      #10;
      if(i >= (FIFO_ALMOST_FULL_THRESHOLD - 1)) begin // at this point, counter is equal to (i - 1)
        if (!almost_full) $error("Error: FIFO should be almost full but it is not.");
      end else begin
        if (almost_full) $error("FIFO is almost full when it should not be.");
      end
    end
    if (!full) $error("Error setting full variable after writing 32 values");

    // Test case 2: Write on full
    $display("Test Case 2: Write on full");
    wr_en = 1;
    fifo_data_in = 20;
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

      rd_en = 1;
      #10;
      // Almost full check
      if(i >= (FIFO_DEPTH - FIFO_ALMOST_FULL_THRESHOLD)) begin
        if (almost_full) $error("Error: FIFO should not be almost full but it is.");
      end else begin
        if (!almost_full) $error("FIFO is not almost full as expected");
      end
      if (fifo_data_out !== i[DATA_WIDTH-1:0]) begin
        $error("Error: Read data does not match expected data!. Read data: %d , expected: %d", fifo_data_out, i[DATA_WIDTH-1:0]);
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
    if (fifo_data_out !== FIFO_DEPTH-1) begin
      $error("Error: Read data should be %d but it is %d", FIFO_DEPTH-1, fifo_data_out);
    end
    rd_en = 0;

    // Test case 5: Write and read in the same cycle
    $display("Test Case 5: Write and read in the same cycle");
    wr_en = 1;
    rd_en = 1;
    // TODO: Possibility of write-through FIFO??
    // Write and read 5 values at the same time, it would be a delay of one clock cycle
    fifo_data_in = 32'h10; // Last read values is 8'h0F, so we start writing from 8'h10
    for (int i=0; i<5; i++) begin
      #10;
      if (fifo_data_out !== fifo_data_in-1) begin // 15/16, 16/17, 17/18, 18/19, 19/20
        $error("Error: Read data does not match written data. Read data: %d, Written data: %d", fifo_data_out, fifo_data_in);
      end
      fifo_data_in = fifo_data_in + 1;
    end
    wr_en = 0;
    rd_en = 0;

    // Test case 7: Clean FIFO
    $display("Test Case 6: Clean FIFO");
    clear = 1; // Clear FIFO before starting the loop
    #10;
    clear = 0; // Clear signal is deasserted
    assert(fifo_data_out === 0) else begin
      $error("Error: FIFO should be cleared but it is not.");
    end

    $display("Test Case 7: Create a loop in FIFO");
    for(int i=0; i<5; i++) begin // Write the fifo with 5 values
      fifo_data_in = i;
      wr_en = 1;
      #10;
    end

    for(int i=0; i<50; i++) begin // Read the fifo with 5 values
      wr_en = $random % 2;
      rd_en = $random % 2;
      loop_en = 1; // Enable loop
      #10;
      assert (fifo_data_out === (i % 5)) else begin
        $error("Error: Read data does not match written data. Read data: %d, Written data: %d", fifo_data_out, i % 5);
      end
    end

    // End simulation
    $display("Testbench completed");
    $finish;
  end

endmodule

