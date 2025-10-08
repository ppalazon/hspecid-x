`timescale 1ns/1ps

module hsid_rst_sync_tb;

  // Clock and reset
  logic clk;
  logic rst_n_async;
  logic rst_n_sync;

  // DUT
  hsid_rst_sync dut (
    .clk(clk),
    .rst_n_async(rst_n_async),
    .rst_n_sync(rst_n_sync)
  );

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_rst_sync_tb);
  end

  // Clock generator (100 MHz)
  initial clk = 1;
  always #5 clk = ~clk; // 10 ns period

  // Async reset stimulus
  initial begin
    // Start with reset asserted
    rst_n_async = 0;
    $display("[%0t] Reset asserted (async)", $time);

    // Hold reset low for some time
    #25;
    rst_n_async = 1;
    $display("[%0t] Reset deasserted (async)", $time);

    // Wait a while
    #80;

    // Apply another async reset pulse, not aligned to clk
    #7  rst_n_async = 0;
    $display("[%0t] Reset asserted again (async)", $time);
    #20 rst_n_async = 1;
    $display("[%0t] Reset deasserted again (async)", $time);

    // Wait some time to see synchronization
    #100;

    $finish;
  end

  // Monitor signals
  initial begin
    $display("    time | clk rst_n_async rst_n_sync");
    $monitor("%8t |  %0b       %0b          %0b",$time, clk, rst_n_async, rst_n_sync);
  end

endmodule
