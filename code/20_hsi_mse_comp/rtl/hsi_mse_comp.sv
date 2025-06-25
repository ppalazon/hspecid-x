`timescale 1ns / 1ps

module hsi_mse_comp #(
    parameter WORD_WIDTH = 32  // Width of the word in bits
  ) (
    input logic clk,
    input logic rst_n,

    // Input mse data
    input logic clear,
    input logic mse_in_valid,  // Enable input MSE data
    input logic [WORD_WIDTH-1:0] mse_in,  // Input MSE

    // Output mse data
    output logic mse_out_valid,  // Enable output MSE data
    output logic [WORD_WIDTH-1:0] mse_out_min,  // Output MSE min
    output logic [WORD_WIDTH-1:0] mse_out_max  // Output MSE max
  );

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mse_out_min <= 32'hFFFFFFFF;  // Reset output min MSE
      mse_out_max <= '0;  // Reset output max MSE\
      mse_out_valid <= 0;  // Disable output MSE valid signal
    end else begin
      if (clear) begin
        mse_out_min <= 32'hFFFFFFFF;  // Reset output min MSE
        mse_out_max <= '0;  // Reset output max MSE
        mse_out_valid <= 0;  // Disable output MSE valid signal
      end else begin
        if (mse_in_valid) begin
          mse_out_valid <= 1;
          if (mse_in <= mse_out_min) begin
            mse_out_min <= mse_in;  // Update min MSE
          end
          if (mse_in >= mse_out_max) begin
            mse_out_max <= mse_in;  // Update max MSE
          end
        end else begin
          mse_out_valid <= 0;  // Disable output MSE valid signal
        end
      end
    end
  end

endmodule