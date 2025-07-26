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

  reg clk;
  reg rst_n;

  // Input initial accumulator value
  reg initial_acc_en;
  reg [DATA_WIDTH_ACC-1:0] initial_acc;

  // Input data
  reg data_in_valid;
  reg [DATA_WIDTH-1:0] data_in_a;
  reg [DATA_WIDTH-1:0] data_in_b;
  reg [HSP_LIBRARY_WIDTH-1:0] data_in_ref; // Reference vector for sum
  reg data_in_last;

  // Output signals
  wire acc_valid;
  wire [DATA_WIDTH_ACC-1:0] acc_value;
  wire acc_last;
  wire [HSP_LIBRARY_WIDTH-1:0] acc_ref; // Reference vector for sum

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
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_valid(data_in_valid),
    .data_in_last(data_in_last),
    .data_in_ref(data_in_ref),
    .data_in_a(data_in_a),
    .data_in_b(data_in_b),
    .acc_valid(acc_valid),
    .acc_value(acc_value),
    .acc_last(acc_last),
    .acc_ref(acc_ref)
  );

  // Random class to generate test vectors
  HsidSqDfAccGen #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH)
  ) sq_df_acc_gen = new();

  // Intermediate sq_df_acc accumulated vector
  logic [DATA_WIDTH_ACC-1:0] acc_vctr [];
  integer pipeline_stages = 3; // Number of pipeline stages in the DUT
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
    data_in_ref = 0; // Initialize reference vector for sum

    #3 rst_n = 0; // Reset the DUT
    #5 rst_n = 1; // Release reset

    for (int i=0; i<10; i++) begin
      if (!sq_df_acc_gen.randomize()) $fatal(0, "Failed to randomize values");

      // Compute the expected accumulated vector
      cycle_count = sq_df_acc_gen.hsp_bands + pipeline_stages; // Reset cycle count for each test
      sq_df_acc_gen.sq_df_acc_vctr(acc_vctr);
      data_in_ref = i[HSP_LIBRARY_WIDTH-1:0]; // Set reference vector for sum
      $display("Test %0d: HSP bands: %0d, Initial acc: %0d, Final acc: %0d", data_in_ref, sq_df_acc_gen.hsp_bands,
        sq_df_acc_gen.initial_acc, acc_vctr[sq_df_acc_gen.hsp_bands-1]);
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
        end

        // Set input data valid signal
        if (count_cycle < sq_df_acc_gen.hsp_bands) begin : data_in
          data_in_valid = cycle_valid_in; // Valid input values
          data_in_a = sq_df_acc_gen.vctr1[count_cycle];
          data_in_b = sq_df_acc_gen.vctr2[count_cycle];
          data_in_last = (count_cycle == sq_df_acc_gen.hsp_bands - 1); // Set band counter for HSI bands
        end else begin
          data_in_valid = 0; // No more valid input values
          data_in_a = 0;
          data_in_b = 0;
          data_in_last = 0; // No more last flag
        end

        if (acc_valid) begin
          assert (acc_value == acc_vctr[count_cycle_valid_out]) else begin
            $error("Test case %0d failed: expected %0d, got %0d at cycle %0d", i, acc_vctr[count_cycle_valid_out], acc_value, count_cycle);
          end
          if (count_cycle_valid_out == sq_df_acc_gen.hsp_bands - 1) begin
            assert (acc_last) else $error("Low `acc_last`: %b on last cycle: %0d", acc_last, count_cycle);
            assert (acc_ref == data_in_ref) else $error("Low `acc_ref`: %0d on last cycle: %0d", acc_ref, count_cycle);
          end
          count_cycle_valid_out++;
        end

        #10; // Wait for one clock cycle
        if (cycle_valid_in) count_cycle++;
      end
    end

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule