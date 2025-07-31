`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_sq_df_acc_tb #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    // parameter TEST_BANDS = HSID_TEST_BANDS, // Length of the vector
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Number of bits for Hyperspectral Pixels (8 bits - 256 bands)
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter TEST_RND_INSERT = 1 // Enable random insertion of test vectors
  );

  localparam logic[DATA_WIDTH_ACC-1:0]    MAX_DATA_ACC = {DATA_WIDTH_ACC{1'b1}}; // Maximum value for accumulator, it's wider than 32 bits
  localparam logic[DATA_WIDTH-1:0]        MAX_DATA = {DATA_WIDTH{1'b1}}; // Maximum value for word width

  reg clk;
  reg rst_n;

  // Clean signal
  reg clear;

  // Input initial accumulator value
  reg initial_acc_en;
  reg [DATA_WIDTH_ACC-1:0] initial_acc;

  // Input data
  reg data_in_valid;
  reg [DATA_WIDTH-1:0] data_in_a;
  reg [DATA_WIDTH-1:0] data_in_b;
  reg data_in_last;

  // Output signals
  wire acc_valid;
  wire [DATA_WIDTH_ACC-1:0] acc_value;
  wire acc_last;
  wire acc_of; // Overflow flag for the accumulated vector

  // Cycle count for the test
  int count_cycle = 0;
  logic cycle_valid_in = 0;
  int count_cycle_valid_out = 0;

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .clear(clear),
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_valid(data_in_valid),
    .data_in_last(data_in_last),
    .data_in_a(data_in_a),
    .data_in_b(data_in_b),
    .acc_valid(acc_valid),
    .acc_value(acc_value),
    .acc_last(acc_last),
    .acc_of(acc_of)
  );

  // Random class to generate test vectors
  HsidHSPixelGen #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) sq_df_acc_gen = new();

  HsidSQDFAccRandom #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) sq_df_acc_random = new();


  // Coverage group for sq_df_acc
  covergroup sq_df_acc_cg @(posedge clk);
    coverpoint clear;
    coverpoint data_in_valid;
    coverpoint data_in_a iff (data_in_valid) {
      bins zero = {0};
      bins max = {MAX_DATA};
      bins middle = {[1:MAX_DATA-1]};
    }
    coverpoint data_in_b iff (data_in_valid) {
      bins zero = {0};
      bins max = {MAX_DATA};
      bins middle = {[1:MAX_DATA-1]};
    }
    coverpoint data_in_last iff (data_in_valid);
    coverpoint initial_acc_en iff (data_in_valid);
    coverpoint initial_acc iff (initial_acc_en) {
      bins zero = {0};
      bins max = {MAX_DATA_ACC};
      bins middle = {[1:MAX_DATA_ACC-1]};
    }
    coverpoint acc_valid;
    coverpoint acc_value iff (acc_valid) {
      bins zero = {0};
      bins middle = {[0:MAX_DATA_ACC-1]};
    }
    coverpoint acc_last iff (acc_valid);
    coverpoint acc_of;
    init_and_last: cross initial_acc_en, data_in_last iff (data_in_valid);
  endgroup

  sq_df_acc_cg sq_df_acc_cov = new();

  // Bind dut to sva assertions
  bind hsid_sq_df_acc hsid_sq_df_acc_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) dut_sva (.*);

  // Intermediate sq_df_acc accumulated vector
  logic [DATA_WIDTH_ACC:0] acc_vctr [];
  logic expected_overflow; // Expected overflow flag for the accumulated vector
  integer pipeline_stages = 4; // Number of pipeline stages in the DUT
  integer cycle_count; // Number of cycles to run the test, vector length + pipeline stages

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_sq_df_acc_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    data_in_valid = 0;
    initial_acc_en = 0;
    initial_acc = 0;
    data_in_a = 0;
    data_in_b = 0;
    data_in_last = 0;
    // data_in_ref = 0; // Initialize reference vector for sum
    clear = 0;

    #3 rst_n = 0; // Reset the DUT
    #5 rst_n = 1; // Release reset

    $display("Case 1: Testing with random values...");
    for (int i=0; i<30; i++) begin
      if (!sq_df_acc_gen.randomize()) $fatal(0, "Failed to randomize values");

      // Compute the expected accumulated vector
      cycle_count = sq_df_acc_gen.hsp_bands + pipeline_stages; // Reset cycle count for each test
      sq_df_acc_gen.sq_df_acc_vctr(acc_vctr);
      expected_overflow = acc_vctr[sq_df_acc_gen.hsp_bands-1][DATA_WIDTH_ACC];
      $display("Test %0d: HSP bands: %0d, Initial acc: %0h, Final acc: %0h, Expected Overflow: %0d", i, sq_df_acc_gen.hsp_bands,
        sq_df_acc_gen.initial_acc, acc_vctr[sq_df_acc_gen.hsp_bands-1], expected_overflow);
      // $display("Test %0d: Vector a: %p", i, sq_df_acc_gen.vctr1);
      // $display("Test %0d: Vector b: %p", i, sq_df_acc_gen.vctr2);
      // $display("Test %0d: Expected accumulated vector: %p", i, acc_vctr);
      // Insert values into the DUT
      count_cycle = 0;
      count_cycle_valid_out = 0;
      while (count_cycle < cycle_count) begin
        // Mark if I should insert a value in this cycle
        cycle_valid_in = (TEST_RND_INSERT == 1) ? $urandom % 2 : 1;

        // Initial accumulator value in the first cycle
        if (count_cycle == 0) begin : set_initial_acc
          initial_acc_en = 1; // Enable initial accumulator value
          initial_acc = sq_df_acc_gen.initial_acc; // Set initial accumulator value
        end else begin
          initial_acc_en = 0; // Disable initial accumulator value
          initial_acc = 0; // Reset initial accumulator value
        end

        // Set input data valid signal
        if (count_cycle < sq_df_acc_gen.hsp_bands) begin : data_in
          data_in_valid = cycle_valid_in; // Valid input values
          data_in_a = sq_df_acc_gen.vctr1[count_cycle];
          data_in_b = sq_df_acc_gen.vctr2[count_cycle];
          data_in_last = (count_cycle == sq_df_acc_gen.hsp_bands - 1); // Set band counter for HSP bands
        end else begin
          data_in_valid = 0; // No more valid input values
          data_in_a = 0;
          data_in_b = 0;
          data_in_last = 0; // No more last flag
        end

        if (acc_valid) begin
          a_int_acc_w_of: assert ({acc_of, acc_value} == acc_vctr[count_cycle_valid_out]) else begin
            $error("Test case %0d failed: expected %0d, got %0d at cycle %0d", i, acc_vctr[count_cycle_valid_out], {acc_of, acc_value}, count_cycle);
          end
          if (count_cycle_valid_out == sq_df_acc_gen.hsp_bands - 1) begin
            a_acc_last: assert (acc_last) else $error("Low `acc_last`: %b on last cycle: %0d", acc_last, count_cycle);
          end
          count_cycle_valid_out++;
        end

        #10; // Wait for one clock cycle
        if (cycle_valid_in) count_cycle++;
      end

      a_of: assert (expected_overflow == acc_of) else $error("Overflow mismatch: expected %0d, got %0d", expected_overflow, acc_of);
    end

    // Test clean signal
    $display("Case 2: Testing clean signal...");
    #10;
    clear = 1; // Enable clean signal
    #10;
    clear = 0; // Disable clean signal
    #10;

    $display("Case 3: Send same vector to check zero accumulations...");
    if(!sq_df_acc_gen.randomize()) $fatal(0, "Failed to randomize values");
    for(int i=0; i<sq_df_acc_gen.hsp_bands; i++) begin
      data_in_valid = 1;
      initial_acc = '0; // Set initial accumulator value
      if (i == 0) begin
        initial_acc_en = 1; // Enable initial accumulator value
      end else begin
        initial_acc_en = 0; // Disable initial accumulator value
      end
      initial_acc = '0; // Set initial accumulator value
      data_in_a = sq_df_acc_gen.vctr1[i]; // Use vector 1 in both inputs
      data_in_b = sq_df_acc_gen.vctr1[i];
      data_in_last = (i == sq_df_acc_gen.hsp_bands - 1); // Set last flag for the last element
      #10; // Wait for one clock cycle
    end

    data_in_valid = 0;

    #20; // Wait for the last cycle to complete
    a_zero_acc_last: assert (acc_last) else $fatal(0, "Low `acc_last`: %b on last cycle, check waiting clock", acc_last);
    a_zero_acc_of: assert (!acc_of) else $error("Overflow flag should be not set, but it is");
    a_zero_acc_value: assert (acc_value == 0) else $error("Accumulator value should be zero, but it is %0h", acc_value);

    $display("Case 4: Trying overflow of overflow values for accumulator...");
    // Initialize values
    // Overflow when 10003 × (ffff × ffff)
    // Overflow of overflow 20005 × (ffff × ffff)
    cycle_count = 'h20007; // It's a huge number to overflow the overflow bit
    for(int i=0; i < cycle_count; i++) begin
      if (i==0) begin
        initial_acc_en = 1;
        initial_acc = '0;
      end else begin
        initial_acc_en = 0;
        initial_acc = 0;
      end
      data_in_valid = 1;
      data_in_a = MAX_DATA;
      data_in_b = '0;
      data_in_last = (i == cycle_count-1);
      #10; // Wait for one clock cycle
    end
    data_in_valid = 0;
    #20; // Wait for the last cycle to complete
    a_max_acc_last: assert (acc_last) else $error("Low `acc_last`: %b on last cycle, check waiting clock", acc_last);
    a_max_acc_of: assert (acc_of) else $error("Overflow flag should be set, but it is not");

    $display("Case 5: Complete random test for sq_df_acc...");
    for (int i = 0; i < 100; i++) begin
      if (!sq_df_acc_random.randomize()) $fatal(0, "Failed to randomize values");
      clear = sq_df_acc_random.clear;
      initial_acc_en = sq_df_acc_random.initial_acc_en;
      initial_acc = sq_df_acc_random.initial_acc;
      data_in_valid = sq_df_acc_random.data_in_valid;
      data_in_a = sq_df_acc_random.data_in_a;
      data_in_b = sq_df_acc_random.data_in_b;
      data_in_last = sq_df_acc_random.data_in_last;
      #10; // Wait for one clock cycle
    end

    #20; // Wait for the last cycle to complete
    data_in_valid = 0;

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule