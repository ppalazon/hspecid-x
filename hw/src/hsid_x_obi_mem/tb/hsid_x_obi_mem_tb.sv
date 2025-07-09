`timescale 1ns / 1ps

// `include "obi/typedef.svh"
// `include "obi/assign.svh"

module hsid_x_obi_mem_tb #(
    parameter TESTS = 30, // Number of tests to run
    parameter RANDOM_GNT = 1 // If set to 1, test_obi_mem will return random grant signals
  ) ();

  localparam WORD_WIDTH = 32;
  // localparam VALUE_MASK = 32'h00003FFF; // Mask to return least significant 14 bits of the address
  localparam VALUE_MASK = 32'h0000FFFF;
  localparam HSI_LIBRARY_SIZE = 8192; // Maximum size of the HSI library
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE); // Address width for HSI library size

  reg clk;
  reg rst_n;
  hsid_x_obi_inf_pkg::obi_req_t obi_req;
  hsid_x_obi_inf_pkg::obi_resp_t obi_rsp;
  reg [WORD_WIDTH-1:0] initial_addr;
  wire data_out_valid;
  wire [WORD_WIDTH-1:0] data_out;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] limit; // Limit for the number of requests
  reg start;
  wire idle;
  wire ready;
  wire done;

  hsid_x_obi_mem #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp),
    .initial_addr(initial_addr),
    .limit(limit),
    .data_out_valid(data_out_valid),
    .data_out(data_out),
    .start(start),
    .idle(idle),
    .ready(ready),
    .done(done)
  );

  // Instantiate a memory OBI subordinate for testing
  test_obi_mem #(
    .RANDOM_GNT(RANDOM_GNT),  // Set to 0 for deterministic behavior
    .RANDOM_VALUE(0), // Set to 0 for deterministic behavior
    .VALUE_MASK(VALUE_MASK) // Mask to return least significant 14 bits of the address
  ) test_obi_mem (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp)
  );

  obi_bus_debug obi_bus_debug (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp)
  );

  int read_addr;
  int reads;


// Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_x_obi_mem_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    initial_addr = 0;
    reads = 0;
    start = 0;
    limit = 0;

    #3 rst_n = 0; // Set reset
    #5 rst_n = 1; // Release reset

    $display("Case 1: Read %0d addresses", TESTS);
    initial_addr = $urandom();
    limit = TESTS;
    perform_reads();

    #10; // Wait for a clock cycle

    $display("Case 2 Address Overflow: Read %0d addresses", TESTS);
    initial_addr = 32'hFFFFFFFF - (2 * (WORD_WIDTH / 8)); // Let 2 addresses before the maximum address
    limit = TESTS;
    perform_reads();

    #10; // Wait for a clock cycle

    $finish;
  end

  always
    #5 clk = ! clk;

  // initial begin
  //   #2000; $finish; // End simulation after a long time to avoid hanging;
  // end

  task assert_dut_state(
      input logic expected_idle,
      input logic expected_ready,
      input logic expected_done
    );
    assert(idle == expected_idle) else $error("ERROR: DUT idle state mismatch. Expected: %0d, Got: %0d", expected_idle, idle);
    assert(ready == expected_ready) else $error("ERROR: DUT ready state mismatch. Expected: %0d, Got: %0d", expected_ready, ready);
    assert(done == expected_done) else $error("ERROR: DUT done state mismatch. Expected: %0d, Got: %0d", expected_done, done);
  endtask

  task perform_reads();
    reads = 0;
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 1;
    #10; // Wait for a clock cycle
    start = 0;
    while (reads < TESTS) begin
      assert_dut_state(0, 1, 0); // Assert DUT is not idle, ready, and not done
      if (data_out_valid) begin
        read_addr = initial_addr + (reads * (WORD_WIDTH / 8));
        if (data_out == (read_addr & VALUE_MASK)) begin
          $display("PASS: %d Data received: 0x%h at address 0x%h", reads, data_out, read_addr);
        end else begin
          $error("ERROR: %d Incorrect data 0x%h at address 0x%h", reads, data_out, read_addr);
        end
        reads++;
      end
      #10;
    end
    assert_dut_state(0, 0, 1); // Assert DUT is not idle, not ready, and done
    assert(reads == TESTS) else $error("ERROR: Not all reads were successful");
    #10;
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
  endtask

endmodule
