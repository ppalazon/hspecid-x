`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_divider_tb #(
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter int K = 4 // You can change K to test different widths
  );

  localparam DK = 2*K;
  localparam MAX_DIVIDEND = {DK{1'b1}};
  localparam MAX_DIVISOR = {K{1'b1}};
  localparam MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}};

  reg clk;
  reg rst_n;
  reg clear;
  reg start;
  reg [DK-1:0] dividend;
  reg [K-1:0] divisor;
  reg of_in;
  reg [HSP_LIBRARY_WIDTH-1:0] hsp_ref_in;
  wire idle;
  wire done;
  wire ready;
  wire [K-1:0] quotient;
  wire [K-1:0] remainder;
  wire overflow;
  wire [HSP_LIBRARY_WIDTH-1:0] hsp_ref_out;

  logic [K-1:0] expected_quotient;
  logic [K-1:0] expected_remainder;
  logic expected_overflow;

  hsid_divider #(
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .K(K)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .clear(clear),
    .start(start),
    .dividend(dividend),
    .divisor(divisor),
    .of_in(of_in),
    .hsp_ref_in(hsp_ref_in),
    .idle(idle),
    .done(done),
    .ready(ready),
    .quotient(quotient),
    .remainder(remainder),
    .overflow(overflow),
    .hsp_ref_out(hsp_ref_out)
  );

  HsidDividerRnd #(
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .K(K)
  ) divider_rnd_gen = new();

  // Covergroup to track coverage of different scenarios
  covergroup cg_divider @(posedge clk);
    coverpoint dividend iff (ready) {
      bins min = {0};
      bins mid = {[1: MAX_DIVIDEND-1]};
      bins divisor = {MAX_DIVISOR};
      bins max = {MAX_DIVIDEND};
    }
    coverpoint divisor iff (ready) {
      bins zero = {0};
      bins min = {1};
      bins mid = {[2: MAX_DIVISOR-1]};
      bins max = {MAX_DIVISOR};
    }
    coverpoint of_in iff (ready);
    coverpoint hsp_ref_in iff (ready) {
      bins zero = {0};
      bins mid = {[1: MAX_HSP_LIBRARY-1]};
      bins max = {MAX_HSP_LIBRARY};
    }
    coverpoint overflow;
    coverpoint quotient iff (done) {
      bins zero = {0};
      bins min = {1};
      bins mid = {[2: MAX_DIVISOR-1]};
      bins max = {MAX_DIVISOR};
    }
    coverpoint remainder iff (done) {
      bins zero = {0};
      bins min = {1};
      bins mid = {[2: MAX_DIVISOR-1]};
    }
    coverpoint hsp_ref_out iff (done) {
      bins zero = {0};
      bins mid = {[1: MAX_HSP_LIBRARY-1]};
      bins max = {MAX_HSP_LIBRARY};
    }
    coverpoint ready;
    coverpoint idle;
    coverpoint done;
  endgroup

  cg_divider cg = new();

  // SVA Bindings
  `ifdef MODEL_TECH
  // Binding SVA assertions to the DUT
  bind hsid_divider hsid_divider_sva #(
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .K(K)
  ) dut_sva (.*);
  `endif

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_divider_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    clear = 0;
    start = 0;
    dividend = 0;
    divisor = 0;

    #3 rst_n = 0; // Set reset
    #5 rst_n = 1; // Release reset

    $display("Case 1: Testing normal operation with random values");
    for (int i=0; i<200; i++) begin
      if (divider_rnd_gen.randomize()) begin
        dividend = divider_rnd_gen.dividend;
        divisor = divider_rnd_gen.divisor;
        of_in = divider_rnd_gen.of_in;
        hsp_ref_in = divider_rnd_gen.hsp_ref_in;

        expected_quotient = divider_rnd_gen.expected_quotient;
        expected_remainder = divider_rnd_gen.expected_remainder;
        expected_overflow = divider_rnd_gen.expected_overflow;

        $display("Test %0d: %0d / %0d = %0d, remainder = %0d, overflow = %b, of_in = %b, hsp_ref = %d", i, dividend, divisor,
          expected_quotient, expected_remainder, expected_overflow, of_in, hsp_ref_in);

        a_idle_bf_start: assert(idle) else $error("Test failed: Not idle before start.");
        a_ready_af_start: assert(ready) else $error("Test failed: Not ready on idle.");

        #10 start = 1; // Start operation
        #10 start = 0; // Clear start signal

        if (expected_overflow) begin
          // #10;
          a_of: assert (overflow) else $error("Test failed: Expected overflow but did not get it.");
          #10;
          a_done_af_of: assert (done) else $error("Test failed: Expected done but did not get it.");
        end else begin
          #((K+1)*10); // Wait for operation to complete
          a_done: assert(done) else $error("Test failed: Operation did not complete as expected.");
          a_quotient: assert(quotient == divider_rnd_gen.expected_quotient) else $error("Test failed: Quotient mismatch. Expected %0d, got %0d", divider_rnd_gen.expected_quotient, quotient);
          a_remainder: assert(remainder == divider_rnd_gen.expected_remainder) else $error("Test failed: Remainder mismatch. Expected %0d, got %0d", divider_rnd_gen.expected_remainder, remainder);
          a_overflow: assert(!overflow) else $error("Test failed: Overflow flag mismatch. Expected %b, got %b", divider_rnd_gen.expected_overflow, overflow);
          a_hsp_ref: assert(hsp_ref_out == hsp_ref_in) else $error("Test failed: HSP reference mismatch. Expected %0d, got %0d", hsp_ref_in, hsp_ref_out);
        end
        #10; // Small delay before next test
        a_idle_af_op: assert(idle) else $error("Test failed: Not idle after operation.");
        a_ready_af_op: assert(ready) else $error("Test failed: Not ready after operation.");
      end
    end

    of_in = 0; // Reset overflow input for next tests

    $display("Case 2: Testing clear after configure");
    dividend = 15;
    divisor = 3;
    assert(idle) else $error("Test failed: Not idle after clear.");
    clear_and_rst(0); // Clear after 0 cycles (next to start)

    $display("Case 3: Testing clear on compute state");
    clear_and_rst(3);

    $display("Case 4: Testing clear on check state");
    clear_and_rst(K);

    $display("Case 5: Start and clear at the same cycle");
    #10 start = 1; clear = 1; // Start and clear at the same time
    #10;
    start = 0; clear = 0; // Clear both signals
    assert(idle) else $error("Test failed: Not idle after start and clear.");

    $display("Case 6: Change inputs while computing");
    #10 start = 1; // Start operation
    #10 start = 0; // Clear start signal
    dividend = 10; // Change inputs while computing
    divisor = 10;
    #((K+1)*10); // Wait for operation to complete
    assert(done) else $error("Test failed: Operation did not complete as expected.");
    assert(quotient == 5) else $error("Test failed: Quotient mismatch after input change. Expected 5, got %0d", quotient);
    assert(remainder == 0) else $error("Test failed: Remainder mismatch after input change. Expected 0, got %0d", remainder);
    assert(!overflow) else $error("Test failed: Overflow flag mismatch after input change. Expected 0, got %b", overflow);
    #10; // Small delay before next test
    assert(idle) else $error("Test failed: Not idle after operation.");

    $display("Case 7: Very short start pulse");
    dividend = 20;
    divisor = 4;
    assert(idle) else $error("Test failed: Not idle after last test.");
    #5 start = 1; // Start operation with a very short pulse
    #5 start = 0; // Clear start signal quickly
    assert(idle) else $error("Test failed: Not idle after short start.");

    $display("All tests completed.");

    #30;
    $finish;

  end

  always
    #5 clk = ! clk;

  task clear_and_rst(input int wait_cycles);
    #10 start = 1; // Start operation
    #10 start = 0;
    #(wait_cycles * 10) clear = 1; // Clear start signal and assert clear
    #10 clear = 0; // Deassert clear
    #10 a_af_clear: assert(idle) else $error("Test failed: Not idle after clear.");

    #10 start = 1; // Start operation
    #10 start = 0;
    #(wait_cycles * 10) rst_n = 0; // Clear start signal and assert clear
    #10 rst_n = 1; // Deassert clear
    a_af_rst: assert(idle) else $error("Test failed: Not idle after clear.");
  endtask

endmodule