`timescale 1ns / 1ps

module test_obi_mem #(
    parameter RANDOM_GNT = 0,  // If set to 1, the response will be random
    parameter RANDOM_VALUE = 0, // If set to 1, the response data will be random
    parameter VALUE_MASK = 32'h00003FFF // Mask to return least significant 14 bits of the address
  ) (
    input logic clk,
    input logic rst_n,

    // OBI interface
    input hsid_x_obi_inf_pkg::obi_req_t obi_req,
    output hsid_x_obi_inf_pkg::obi_resp_t obi_rsp
  );

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      obi_rsp.rvalid <= 1'b0;
      obi_rsp.rdata <= '0;
      obi_rsp.gnt <= 1'b1;
    end else begin
      if (RANDOM_GNT) begin
        obi_rsp.gnt <= $random % 2; // Random grant signal
      end else begin
        obi_rsp.gnt <= 1;
      end
      if (obi_rsp.gnt && obi_req.req) begin
        obi_rsp.rvalid <= 1'b1;
        if (RANDOM_VALUE) begin
          obi_rsp.rdata <= $random(); // Random response data
        end else begin
          obi_rsp.rdata <= obi_req.addr & VALUE_MASK; // Return least significant 14 bits of the address
        end
      end else begin
        obi_rsp.rvalid <= 1'b0;
      end
    end
  end

endmodule