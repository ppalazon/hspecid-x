`timescale 1ns / 1ps

module hsid_sq_df #(
    parameter DATA_WIDTH = 16  // 16 bits by default
  ) (
    input logic clk,
    input logic rst_n,

    input logic [DATA_WIDTH-1:0] data_in_v1, // Input vector 1
    input logic [DATA_WIDTH-1:0] data_in_v2, // Input vector 2
    output logic [(DATA_WIDTH*2)-1:0] data_out // Output result
  );

  logic [DATA_WIDTH-1:0] diff; // Difference between bands

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      data_out <= 0; // Reset output data
      diff <= 0; // Reset difference
    end else begin
      diff <= data_in_v1 - data_in_v2; // Compute difference
      data_out <= diff * diff; // Compute squared difference
    end
  end
endmodule