`timescale 1ns / 1ps

module obi_bus_debug(
    input logic clk,
    input logic rst_n,
    input wire hsid_x_obi_inf_pkg::obi_req_t obi_req,
    input wire hsid_x_obi_inf_pkg::obi_resp_t obi_rsp
  );

  logic        req;
  logic        we;
  logic [3:0]  be;
  logic [31:0] addr;
  logic [31:0] wdata;

  logic        gnt;
  logic        rvalid;
  logic [31:0] rdata;


  assign req = obi_req.req;
  assign we = obi_req.we;
  assign be = obi_req.be;
  assign addr = obi_req.addr;
  assign wdata = obi_req.wdata;

  assign gnt = obi_rsp.gnt;
  assign rvalid = obi_rsp.rvalid;
  assign rdata = obi_rsp.rdata;


endmodule