`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_fifo_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // 32 bits by default
    parameter FIFO_ADDR_WIDTH = HSID_FIFO_ADDR_WIDTH, // Address width for FIFO depth
    parameter FIFO_ALMOST_FULL_THRESHOLD = 10 // Optional threshold for almost full
  );

  // Local parameters
  localparam FIFO_DEPTH = 2 ** FIFO_ADDR_WIDTH; // Define FIFO depth based on address width

  // Signals
  reg clk;
  reg rst_n;
  reg wr_en;
  reg rd_en;
  reg loop_en = 0;
  reg [WORD_WIDTH-1:0] fifo_data_in;
  reg [FIFO_ADDR_WIDTH-1:0] almost_full_threshold = FIFO_ALMOST_FULL_THRESHOLD; // Element to process
  wire [WORD_WIDTH-1:0] fifo_data_out;
  wire full;
  wire almost_full;
  wire empty;
  reg clear;

  // Instantiate the FIFO module
  hsid_fifo #(
    .WORD_WIDTH(WORD_WIDTH),
    .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) dut (
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

  `ifdef MODEL_TECH
  // bind verification to the DUT instance
  bind hsid_fifo hsid_fifo_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) dut_sva (.*);
  `endif

  // covergroup for FIFO
  covergroup fifo_cg @(posedge clk);
    coverpoint full;
    coverpoint almost_full;
    coverpoint empty;
    coverpoint loop_en;
    coverpoint wr_en;
    coverpoint rd_en;
    coverpoint clear;
    coverpoint almost_full_threshold;

    read_on_empty: cross rd_en, empty;
    write_on_full: cross wr_en, full;
    all_commands: cross wr_en, rd_en, loop_en;
    write_and_read_on_empty: cross wr_en, rd_en, empty; // Try to read and write when FIFO is empty (in this case only write should be enabled)
    loop_on_empty: cross loop_en, empty; // Try to loop when FIFO is empty (in this case only loop should be enabled)
    loop_on_full: cross loop_en, full; // Try to loop when FIFO is full (in this case only loop should be enabled)
    write_on_almost_full: cross wr_en, almost_full; // Try to write when FIFO is almost full (in this case only read should be enabled)
    read_on_full: cross rd_en, full; // Try to read when FIFO is full (in this case only write should be enabled)
    clear_on_full: cross clear, full; // Try to clear when FIFO is full (in this case FIFO should be cleared)
    clear_on_empty: cross clear, empty; // Try to clear when FIFO is empty (in this case FIFO should be cleared)
  endgroup

  fifo_cg fifo_cov = new;

  hsid_fifo_op #(
    .WORD_WIDTH(WORD_WIDTH),
    .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) random_op = new();

  // Generate a queue
  logic [WORD_WIDTH-1:0] fifo_values[$];
  logic [WORD_WIDTH-1:0] fifo_value_expected;
  logic fifo_value_check_read;
  logic fifo_value_check_loop;

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
    clk = 1;
    rst_n = 1;
    wr_en = 0;
    rd_en = 0;
    fifo_data_in = 0;
    clear = 0;
    loop_en = 0;

    // Reset the FIFO
    #3 rst_n = 0;
    #5 rst_n = 1;

    repeat(100) begin
      // Random generate operations
      if(!random_op.randomize()) $fatal(0, "Randomization failed");

      $display("Operations %0d: wr_en=%0d, rd_en=%0d, clear=%0d, loop_en=%0d, data_in=%h, almost_full_threshold=%0d",
        random_op.repeat_op, random_op.wr_en, random_op.rd_en, random_op.clear, random_op.loop_en,
        random_op.data_in, random_op.almost_full_threshold);

      for (int i = 0; i < random_op.repeat_op; i++) begin
        clear = random_op.clear;
        wr_en = random_op.wr_en;
        rd_en = random_op.rd_en;
        loop_en = random_op.loop_en;
        almost_full_threshold = random_op.almost_full_threshold;
        fifo_data_in = random_op.data_in;
        if(!clear && !loop_en && wr_en && !full) begin
          fifo_values.push_back(fifo_data_in); // Save the value to the fifo_values queue
        end
        fifo_value_check_read = !clear && !empty && !loop_en && rd_en;
        fifo_value_check_loop = !clear && !empty && loop_en;
        #10; // Wait for one clock cycle
        if (fifo_value_check_read) begin
          if (fifo_values.size() == 0) $fatal(0, "Error: FIFO values queue is empty when it should not be");
          fifo_value_expected = fifo_values.pop_front();
          assert (fifo_data_out == fifo_value_expected) else begin
            $error("Error: Read data does not match expected data. Read data: %h, Expected: %h", fifo_data_out, fifo_value_expected);
          end
        end
        if (fifo_value_check_loop) begin
          if (fifo_values.size() == 0) $fatal(0, "Error: FIFO values queue is empty when it should not be");
          fifo_value_expected = fifo_values.pop_front(); // Loop operation, expect the same value
          fifo_values.push_back(fifo_value_expected); // Push the value back to the queue
        end
        if (clear) begin
          fifo_values.delete(); // Clear the queue
        end
      end
    end

    // End simulation
    $display("Testbench completed");
    $finish;
  end

endmodule

