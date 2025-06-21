`timescale 1ns / 1ps

module sq_df_tb;

  reg clk;
  reg rst_n;
  reg [`DATA_WIDTH-1:0] data_in_v1;
  reg [`DATA_WIDTH-1:0] data_in_v2;
  wire [(`DATA_WIDTH*2)-1:0] data_out;

  sq_df #(
    .DATA_WIDTH(`DATA_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_v1(data_in_v1),
    .data_in_v2(data_in_v2),
    .data_out(data_out)
  );

  initial
  begin
    clk = 1;
    rst_n = 1;
    data_in_v1 = 0;
    data_in_v2 = 0;

    #10 rst_n = 0; // Reset the DUT
    #10 rst_n = 1; // Release reset

    // Test case 1: 5 - 3 = 2, squared = 4
    data_in_v1 = 5;
    data_in_v2 = 3;
    #20;
    if (data_out !== 4) begin
      $display("Test case 1 failed: expected 4, got %0d", data_out);
    end else begin
      $display("Test case 1 passed");
    end

    $finish; // End simulation
  end

  always
    #5 clk = ! clk;

endmodule