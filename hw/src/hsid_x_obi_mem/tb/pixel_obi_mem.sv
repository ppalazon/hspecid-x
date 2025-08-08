`timescale 1ns / 1ps

import hsid_pkg::*;

module pixel_obi_mem #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // Pixel data width
    parameter VALUE_MASK = 32'h00003FFF // Mask to return least significant 14 bits of the address
  ) (
    input logic clk,
    input logic rst_n,

    // OBI interface
    input wire hsid_x_obi_inf_pkg::obi_req_t obi_req,
    output var hsid_x_obi_inf_pkg::obi_resp_t obi_rsp,

    input logic random_gnt // Random grant signal
  );

  logic [DATA_WIDTH-1:0] lsb_pixel_value;
  logic [DATA_WIDTH-1:0] msb_pixel_value;
  // logic [DATA_WIDTH-1:0] da_pixel_value;


  assign msb_pixel_value = (obi_req.addr[WORD_WIDTH-1:DATA_WIDTH] & VALUE_MASK);
  assign lsb_pixel_value = (obi_req.addr[DATA_WIDTH-1:0] & VALUE_MASK);
  // assign da_pixel_value = (da_addr[DATA_WIDTH-1:0] & VALUE_MASK);
  // assign da_data = RANDOM_VALUE ? $random() : {da_pixel_value, da_pixel_value}; // Return random data or masked address

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      obi_rsp.rvalid <= 1'b0;
      obi_rsp.rdata <= '0;
      obi_rsp.gnt <= 1'b0;
    end else begin
      if (obi_req.req) begin
        if (random_gnt) begin : is_random_grant
          if ($random % 2) begin : random_grant
            obi_rsp.gnt <= 1'b1;
          end else begin : random_no_grant
            obi_rsp.gnt <= 1'b0;
          end
        end else begin : is_fixed_grant
          obi_rsp.gnt <= 1'b1;
        end
      end
      if(obi_req.req && obi_rsp.gnt) begin : after_grant
        obi_rsp.rvalid <= 1'b1;
        obi_rsp.rdata <= {lsb_pixel_value, msb_pixel_value}; // Return least significant 14 bits of the address
      end else begin
        obi_rsp.rvalid <= 1'b0;
      end
    end
  end

endmodule