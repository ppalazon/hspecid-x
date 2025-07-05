`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_sq_df_acc_tb;

  localparam DATA_WIDTH = HSID_DATA_WIDTH; // 16 bits by default
  localparam DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL;
  localparam DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC;
  localparam VECTOR_LENGTH = HSID_VECTOR_LENGTH_TB; // Length of the vector
  localparam HSI_LIBRARY_SIZE = HSID_HSI_LIBRARY_SIZE; // Size of the HSI library
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);

  reg clk;
  reg rst_n;

  // Input initial accumulator value
  reg initial_acc_en;
  reg [DATA_WIDTH_ACC-1:0] initial_acc;

  // Input data
  reg data_in_valid;
  reg [DATA_WIDTH-1:0] data_in_a;
  reg [DATA_WIDTH-1:0] data_in_b;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] data_in_ref; // Reference vector for sum
  reg data_in_last;

  // Output signals
  wire acc_valid;
  wire [DATA_WIDTH_ACC-1:0] acc_value;
  wire acc_last;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] acc_ref; // Reference vector for sum

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
  HsidSqDfAccGen sq_df_acc_gen = new();

  // Intermediate sq_df_acc accumulated vector
  logic [DATA_WIDTH_ACC-1:0] acc_vctr [0:VECTOR_LENGTH-1];
  integer pipeline_stages = 3; // Number of pipeline stages in the DUT
  integer cycle_count = VECTOR_LENGTH + pipeline_stages; // Number of cycles to run the test, vector length + pipeline stages

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
    #7 rst_n = 1; // Release reset

    for (int i=0; i<3; i++) begin
      if (sq_df_acc_gen.randomize()) begin
        // Compute the expected accumulated vector
        sq_df_acc_gen.sq_df_acc_vctr(acc_vctr);

        data_in_ref = i % HSI_LIBRARY_SIZE; // Set reference vector for sum
        // Insert values into the DUT
        for (int cycle=0; cycle<cycle_count; cycle++) begin
          // Initial accumulator value in the first cycle
          if (cycle == 0) begin : set_initial_acc
            initial_acc_en = 1; // Enable initial accumulator value
            initial_acc = sq_df_acc_gen.initial_acc; // Set initial accumulator value
          end else begin
            initial_acc_en = 0; // Disable initial accumulator value
          end

          // Set input data valid signal
          if (cycle < VECTOR_LENGTH) begin : data_in
            data_in_valid = 1; // Valid input values
            data_in_a = sq_df_acc_gen.vctr1[cycle];
            data_in_b = sq_df_acc_gen.vctr2[cycle];
            data_in_last = (cycle == VECTOR_LENGTH - 1); // Set band counter for HSI bands
          end else begin
            data_in_valid = 0; // No more valid input values
            data_in_a = 0;
            data_in_b = 0;
            data_in_last = 0; // No more last flag
          end

          // Read output data and check validity
          if (cycle >= pipeline_stages) begin : output_check
            if(cycle == VECTOR_LENGTH + pipeline_stages) begin
              assert (acc_last) else $error("Low `acc_last` on last cycle: %0d", cycle);
            end
            assert (data_in_ref == acc_ref) else begin
              $error("Reference vector mismatch at cycle %0d: expected %0d, got %0d", cycle, data_in_ref, acc_ref);
            end
            if (acc_valid) begin
              if (acc_value !== acc_vctr[cycle - pipeline_stages]) begin
                $error("Test case %0d failed: expected %0d, got %0d at cycle %0d", i, acc_vctr[cycle - pipeline_stages], acc_value, cycle);
              end else begin
                $display("Test case %0d passed at cycle %0d", i, cycle);
              end
            end else begin
              $error("Output not valid at cycle %0d", cycle);
            end
          end else begin
            if (acc_valid) begin
              $error("Output valid before pipeline stages at cycle %0d", cycle);
            end
          end

          #10; // Wait for one clock cycle
        end
      end
    end

    $finish;
  end

  always
    #5 clk = ! clk;

endmodule