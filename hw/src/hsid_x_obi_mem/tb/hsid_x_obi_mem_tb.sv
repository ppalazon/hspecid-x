`timescale 1ns / 1ps

// `include "obi/typedef.svh"
// `include "obi/assign.svh"

module hsid_x_obi_mem_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // Data width for the pixel memory
    parameter MEM_ACCESS_WIDTH = HSID_MEM_ACCESS_WIDTH, // Address width for HSI library size
    parameter VALUE_MASK = 32'h0000FFFF, // Mask to return least significant 16 bits of the address
    parameter VALUE_MODULE_LSB = 13,
    parameter VALUE_MODULE_MSB = 17
  ) ();

  localparam MAX_MEM_ACCESS = {MEM_ACCESS_WIDTH{1'b1}};

  reg clk;
  reg rst_n;
  hsid_x_obi_inf_pkg::obi_req_t obi_req;
  hsid_x_obi_inf_pkg::obi_resp_t obi_rsp;
  reg [WORD_WIDTH-1:0] initial_addr;
  wire data_out_valid;
  wire [WORD_WIDTH-1:0] data_out;
  reg [MEM_ACCESS_WIDTH-1:0] limit; // Limit for the number of requests
  reg def_gnt; // Default grant signal for the OBI bus when there is no request
  reg random_gnt; // Random grant signal
  reg clear;
  reg start;
  wire idle;
  wire ready;
  wire done;

  // Device Under Test (DUT)
  hsid_x_obi_mem #(
    .WORD_WIDTH(WORD_WIDTH),
    .MEM_ACCESS_WIDTH(MEM_ACCESS_WIDTH)
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
    .clear(clear),
    .idle(idle),
    .ready(ready),
    .done(done)
  );

  // Instantiate a memory OBI subordinate for testing
  hsp_obi_mem #(
    .DATA_WIDTH(DATA_WIDTH), // Data width for the pixel memory
    .VALUE_MASK(VALUE_MASK), // Mask to return least significant 14 bits of the address
    .VALUE_MODULE_LSB(VALUE_MODULE_LSB), // Apply the mask and then modulo to get the value
    .VALUE_MODULE_MSB(VALUE_MODULE_MSB)
  ) hsp_obi_mem_inst (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp),
    .random_gnt(random_gnt),
    .def_gnt(def_gnt)
  );

  // Module to debug the OBI bus
  obi_bus_debug obi_bus_debug (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp)
  );

  // Generate a random number of requests
  HsidXObiMemRandom #(
    .WORD_WIDTH(WORD_WIDTH),
    .MEM_ACCESS_WIDTH(MEM_ACCESS_WIDTH)
  ) hsid_x_obi_mem_random = new();

  // Coverage group for OBI memory
  covergroup hsid_x_obi_mem_cg @(posedge clk);
    coverpoint idle;
    coverpoint ready;
    coverpoint done;
    coverpoint start iff (idle);
    coverpoint clear iff (idle);
    coverpoint initial_addr iff (!idle && !ready && !done) { // On init state
      bins addr_low  = { [32'h0000_0000 : 32'h5555_5554] }; // 0 .. 0x5555_5554
      bins addr_mid  = { [32'h5555_5555 : 32'hAAAA_AAA9] }; // 0x5555_5555 .. 0xAAAA_AAA9
      bins addr_high = { [32'hAAAA_AAAA : 32'hFFFF_FFFF] }; // 0xAAAA_AAAA .. 0xFFFF_FFFF
    }
    coverpoint limit iff (!idle && !ready && !done) { // On init state
      bins zero = {0};
      bins max = {MAX_MEM_ACCESS};
      bins mid = {[1:MAX_MEM_ACCESS-1]};
    }
    coverpoint data_out_valid;

    start_clear: cross start, clear iff (idle);
  endgroup

  hsid_x_obi_mem_cg hsid_x_obi_mem_cov = new;

  `ifdef MODEL_TECH
  // Binding SVA modules
  bind hsid_x_obi_mem hsid_x_obi_mem_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .MEM_ACCESS_WIDTH(MEM_ACCESS_WIDTH)
  ) hsid_x_obi_mem_sva_inst (.*);
  `endif

  logic[MEM_ACCESS_WIDTH-1:0] requests;
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
    clear = 0;
    random_gnt = 0;
    def_gnt = 0;

    #3 rst_n = 0; // Set reset
    #5 rst_n = 1; // Release reset


    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = hsid_x_obi_mem_random.initial_addr;
    limit = hsid_x_obi_mem_random.requests;
    $display("Case 1: Read %0d addresses from 0x%0h", limit, initial_addr);
    perform_reads();

    #10; // Wait for a clock cycle

    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = 32'hFFFFFFFF - (2 * (WORD_WIDTH / 8)); // Let 2 addresses before the maximum address
    limit = hsid_x_obi_mem_random.requests;
    $display("Case 2: Address will overflow: Read %0d addresses from 0x%0h", limit, initial_addr);
    perform_reads();

    #10; // Wait for a clock cycle

    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = hsid_x_obi_mem_random.initial_addr;
    limit = hsid_x_obi_mem_random.requests;
    random_gnt = 1; // Enable random grant signal
    $display("Case 3: Read %0d addresses with random grant from 0x%0h", limit, initial_addr);
    perform_reads();

    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = hsid_x_obi_mem_random.initial_addr;
    limit = MAX_MEM_ACCESS;
    random_gnt = 1; // Enable random grant signal
    $display("Case 4: Read %0d (Maximum) addresses with random grant from 0x%0h", limit, initial_addr);
    perform_reads();

    #10;

    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = hsid_x_obi_mem_random.initial_addr;
    limit = hsid_x_obi_mem_random.requests;
    random_gnt = 1; // Enable random grant signal
    $display("Case 5: Read %0d addresses with clear just after start from 0x%0h", limit, initial_addr);
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 1; clear = 0;
    #10;
    assert_dut_state(0, 0, 0); // Assert DUT is not idle, ready, and not done (INIT State)
    start = 0; clear = 1;
    #10;
    assert_dut_state(0, 0, 0); // Assert DUT is not idle, ready, and not done (CLEAR State)
    start = 0; clear = 0;
    #10;
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done


    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = hsid_x_obi_mem_random.initial_addr;
    limit = hsid_x_obi_mem_random.requests;
    random_gnt = 1; // Enable random grant signal
    $display("Case 6: Read %0d addresses with clear in the middle of reading", limit);
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 1; clear = 0;
    #((limit/2) * 10); // Wait for half of the requests
    assert_dut_state(0, 1, 0); // Assert DUT is not idle, ready, and not done
    start = 0; clear = 1;
    #10;
    assert_dut_state(0, 0, 0); // Assert DUT is not idle, ready, and not done
    start = 0; clear = 0;
    #10;
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done

    $display("Case 7: Set start and clear at the same time in IDLE state");
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 1; clear = 1;
    #10;
    assert_dut_state(1, 0, 0); // Assert DUT is still idle, not ready, and not done
    start = 0; clear = 0;

    $display("Case 8: Test clear on IDLE state");
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    clear = 1;
    #10;
    assert_dut_state(1, 0, 0); // Assert DUT is still idle, not ready, and not done
    clear = 0;

    $display("Case 9: Set limit to 0 and start reading, and then clear");
    if (!hsid_x_obi_mem_random.randomize()) $fatal(0, "Randomization failed");
    initial_addr = hsid_x_obi_mem_random.initial_addr;
    limit = 0; // Set limit to 0
    random_gnt = 1; // Enable random grant signal
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 1; clear = 0;
    #20; // Wait for two clock cycle (init and reading)
    assert_dut_state(0, 1, 0); // Assert DUT is not idle, ready, and not done
    #100;
    start = 0; clear = 1; // Clear the DUT
    #20; // Wait for two clock cycles (clean and idle)
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 0; clear = 0; // Reset start and clear


    #20; // Wait before finishing the simulation

    $finish;
  end

  always
    #5 clk = ! clk;

// initial begin
//   #2000000; $finish; // End simulation after a long time to avoid hanging;
// end

  task assert_dut_state(
      input logic expected_idle,
      input logic expected_ready,
      input logic expected_done
    );
    a_idle_exp: assert(idle == expected_idle) else $error("ERROR: DUT idle state mismatch. Expected: %0d, Got: %0d", expected_idle, idle);
    a_ready_exp: assert(ready == expected_ready) else $error("ERROR: DUT ready state mismatch. Expected: %0d, Got: %0d", expected_ready, ready);
    a_done_exp: assert(done == expected_done) else $error("ERROR: DUT done state mismatch. Expected: %0d, Got: %0d", expected_done, done);
  endtask

  task perform_reads();
    requests = limit;
    reads = 0;
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
    start = 1;
    #10; // Wait for a clock cycle
    start = 0;
    #10; // Wait for a clock cycle for INIT state
    while (reads < requests) begin
      assert_dut_state(0, 1, 0); // Assert DUT is not idle, ready, and not done
      if (data_out_valid) begin
        read_addr = initial_addr + (reads * (WORD_WIDTH / 8));
        a_addr_data: assert (data_out == addr_value(read_addr)) else begin
          $error("ERROR: %d Incorrect data 0x%h at address 0x%h", reads, data_out, read_addr);
        end
        reads++;
      end
      #10;
    end
    assert_dut_state(0, 0, 1); // Assert DUT is not idle, not ready, and done
    a_finish_reads: assert(reads == requests) else $error("ERROR: Not all reads were successful");
    #10;
    assert_dut_state(1, 0, 0); // Assert DUT is idle, not ready, and not done
  endtask

  function logic [31:0] addr_value(logic [WORD_WIDTH-1:0] addr);
    logic [DATA_WIDTH-1:0] msb_masked_addr;
    logic [DATA_WIDTH-1:0] lsb_masked_addr;
    lsb_masked_addr = (addr[DATA_WIDTH-1:0] & VALUE_MASK) % VALUE_MODULE_LSB; // Mask to return least significant 14 bits of the address
    msb_masked_addr = (addr[DATA_WIDTH-1:0] & VALUE_MASK) % VALUE_MODULE_MSB; // Mask to return least significant 14 bits of the address
    // msb_masked_addr = (addr[WORD_WIDTH-1:DATA_WIDTH] & VALUE_MASK) % VALUE_MODULE_LSB; // Mask to return least significant 14 bits of the address
    return {msb_masked_addr, lsb_masked_addr}; // Return least significant 14 bits of the address
  endfunction

endmodule
