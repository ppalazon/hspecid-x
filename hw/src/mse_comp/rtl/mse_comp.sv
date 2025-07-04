`timescale 1ns / 1ps

module mse_comp #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter HSI_LIBRARY_SIZE = 256,
    parameter HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)  // Number of bits for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    // Input mse data
    input logic clear,
    input logic mse_in_valid,  // Enable input MSE data
    input logic [WORD_WIDTH-1:0] mse_in_value,  // Input MSE
    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_in_ref,

    // Output mse data
    output logic mse_out_valid,  // Enable output MSE data
    output logic [WORD_WIDTH-1:0] mse_min_value,
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref,
    output logic mse_min_changed,
    output logic [WORD_WIDTH-1:0] mse_max_value,
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref,
    output logic mse_max_changed
  );

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mse_clear();  // Clear all MSE values and flags
    end else begin
      if (clear) begin
        mse_clear();  // Clear all MSE values and flags
      end else begin
        if (mse_in_valid) begin
          mse_out_valid <= 1;
          if (mse_in_value <= mse_min_value) begin
            mse_min_changed <= 1;  // Set min changed flag
            mse_min_ref <= mse_in_ref;  // Update min reference MSE
            mse_min_value <= mse_in_value;  // Update min MSE
          end else begin
            mse_min_changed <= 0;  // Reset min changed flag
          end
          if (mse_in_value >= mse_max_value) begin
            mse_max_changed <= 1;  // Set max changed flag
            mse_max_ref <= mse_in_ref;  // Update max reference MSE
            mse_max_value <= mse_in_value;  // Update max MSE
          end else begin
            mse_max_changed <= 0;  // Reset max changed flag
          end
        end else begin
          mse_out_valid <= 0;  // Disable output MSE valid signal
          mse_min_changed <= 0;
          mse_max_changed <= 0;
        end
      end
    end
  end

  task mse_clear();
    begin
      mse_min_value <= 32'hFFFFFFFF;  // Reset output min MSE
      mse_max_value <= '0;  // Reset output max MSE
      mse_out_valid <= 0;  // Disable output MSE valid signal
      mse_min_ref <= '0;  // Reset output min reference MSE
      mse_max_ref <= '0;  // Reset output max reference MSE
      mse_min_changed <= 0;  // Reset min changed flag
      mse_max_changed <= 0;  // Reset max changed flag
    end
  endtask

endmodule