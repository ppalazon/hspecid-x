`timescale 1ns / 1ps

import hsi_mse_pkg::*;

module sq_df_acc_tb;

  localparam DATA_WIDTH = HM_DATA_WIDTH; // 16 bits by default
  localparam DATA_WIDTH_MUL = HM_DATA_WIDTH_MUL;
  localparam DATA_WIDTH_ACC = HM_DATA_WIDTH_ACC;
  localparam VECTOR_LENGTH = HM_VECTOR_LENGTH_TB; // Length of the vector

  reg clk;
  reg rst_n;

  // Input initial accumulator value
  reg initial_acc_en;
  reg [DATA_WIDTH_ACC-1:0] initial_acc;

  // Input data
  reg data_in_valid;
  reg [DATA_WIDTH-1:0] data_in_v1;
  reg [DATA_WIDTH-1:0] data_in_v2;

  // Output signals
  wire data_out_valid;
  wire [DATA_WIDTH_ACC-1:0] data_out;

  sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(data_in_valid),
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_v1(data_in_v1),
    .data_in_v2(data_in_v2),
    .data_out_valid(data_out_valid),
    .data_out(data_out)
  );

  // Random class to generate test vectors
  SqDfAccGen sq_df_acc_gen = new();

  // Intermediate sq_df_acc accumulated vector
  logic [DATA_WIDTH_ACC-1:0] acc_vctr [0:VECTOR_LENGTH-1];
  integer pipeline_stages = 3; // Number of pipeline stages in the DUT
  integer cycle_count = VECTOR_LENGTH + pipeline_stages; // Number of cycles to run the test, vector length + pipeline stages

  initial
  begin
    clk = 1;
    rst_n = 1;
    data_in_valid = 0;
    initial_acc_en = 0;
    initial_acc = 0;
    data_in_v1 = 0;
    data_in_v2 = 0;

    #3 rst_n = 0; // Reset the DUT
    #7 rst_n = 1; // Release reset

    for (int i=0; i<3; i++) begin
      if (sq_df_acc_gen.randomize()) begin
        // Compute the expected accumulated vector
        sq_df_acc_gen.sq_df_acc_vctr(acc_vctr);

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
            data_in_v1 = sq_df_acc_gen.vctr1[cycle];
            data_in_v2 = sq_df_acc_gen.vctr2[cycle];
          end else begin
            data_in_valid = 0; // No more valid input values
            data_in_v1 = 0;
            data_in_v2 = 0;
          end

          // Read output data and check validity
          if (cycle >= pipeline_stages) begin : output_check
            if (data_out_valid) begin
              // Check if the output matches the expected accumulated vector
              if (data_out !== acc_vctr[cycle - pipeline_stages]) begin
                $error("Test case %0d failed: expected %0d, got %0d at cycle %0d", i, acc_vctr[cycle - pipeline_stages], data_out, cycle);
              end else begin
                $display("Test case %0d passed at cycle %0d", i, cycle);
              end
            end else begin
              $error("Output not valid at cycle %0d", cycle);
            end
          end else begin
            if (data_out_valid) begin
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