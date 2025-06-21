import hsi_mse_pkg::*;

module sq_df_acc #(
    parameter DATA_WIDTH = HM_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HM_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HM_DATA_WIDTH_ACC // Data width for accumulator, larger than DATA_WIDTH
  ) (
    input logic clk,
    input logic rst_n,

    input logic initial_acc_en,                   // Enable initial accumulator value
    input logic [DATA_WIDTH_ACC-1:0] initial_acc, // Initial accumulator value

    input logic data_in_valid, // Valid input values
    input logic signed [DATA_WIDTH-1:0] data_in_v1, // Input vector 1
    input logic signed [DATA_WIDTH-1:0] data_in_v2, // Input vector 2

    output logic data_out_valid, // Output enable signal
    output logic [DATA_WIDTH_ACC-1:0] data_out // Output result
  );

  logic en_1, en_2, en_3; // Enable signals for pipeline stages

  logic acc_1_en, acc_2_en; // Enable signals for accumulators
  logic [DATA_WIDTH_ACC-1:0] acc_1, acc_2; // Accumulators for pipeline stages

  logic signed [DATA_WIDTH:0] diff; // Difference between elements, using one extra bit for overflow
  logic [DATA_WIDTH_MUL-1:0] mult;
  logic [DATA_WIDTH_ACC-1:0] acc; // Multipy and accumulator for the output

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      diff <= 0; // Reset difference
      en_1 <= 0; // Reset stage 1
      en_2 <= 0; // Reset enable signal
      en_3 <= 0; // Reset stage 3
      acc <= 0; // Reset accumulator to initial value
      mult <= 0; // Reset multiplication result
      acc_1 <= 0; // Reset stage 1 accumulator
      acc_2 <= 0; // Reset stage 2 accumulator
      acc_1_en <= 0; // Disable initial accumulator value
      acc_2_en <= 0; // Disable stage 2 accumulator
      data_out <= 0; // Reset output data
      data_out_valid <= 0; // Disable output
    end else begin
      if (data_in_valid) begin : enable_stage_1
        en_1 <= 1;
        acc_1_en <= initial_acc_en; // Enable initial accumulator value
        acc_1 <= initial_acc; // Set initial accumulator value
        diff <= data_in_v1 - data_in_v2; // Compute difference
      end else begin : disable_stage_1
        en_1 <= 0; // Disable stage 1
        acc_1_en <= 0; // Disable initial accumulator value
      end
      if (en_1) begin : enable_stage_2
        en_2 <= 1;
        acc_2_en <= acc_1_en; // Propagate enable signal for accumulator
        acc_2 <= acc_1; // Propagate accumulator value
        mult <= diff * diff; // Compute squared difference and accumulate
      end else begin : disable_stage_2
        en_2 <= 0; // Disable stage 2
        acc_2_en <= 0; // Disable accumulator
      end
      if (en_2) begin : enable_stage_3
        data_out_valid <= 1; // Enable output when all stages are ready
        if(acc_2_en) begin : use_initial_acc
          data_out <= acc_2 + mult; // Add to initial accumulator value
        end else begin
          data_out <= data_out + mult; // Add to initial accumulator value
        end
      end else begin : disable_stage_3
        data_out_valid <= 0;
      end

      // The folling code add a new stage to the pipeline, but I think it is not necessary
      // if (en_2) begin : enable_stage_3
      //   en_3 <= 1;
      //   if(acc_2_en) begin : use_initial_acc
      //     acc <= acc_2 + mult; // Add to initial accumulator value
      //   end else begin
      //     acc <= acc + mult; // Add to initial accumulator value
      //   end
      // end else begin : disable_stage_3
      //   en_3 <= 0; // Disable stage 3
      // end
      // if (en_3) begin
      //   data_out_valid <= 1; // Enable output when all stages are ready
      //   data_out <= acc; // Output the final accumulated value
      // end else begin
      //   data_out_valid <= 0; // Disable output
      // end
    end
  end
endmodule