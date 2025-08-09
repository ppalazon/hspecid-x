`timescale 1ns/1ps

module reg_inf_debug(
    input logic clk,
    input logic rst_n,

    input wire hsid_x_reg_pkg::reg_req_t reg_req,
    input wire hsid_x_reg_pkg::reg_rsp_t reg_rsp
  );

  logic        valid;
  logic        write;
  logic [3:0]  wstrb;
  logic [31:0] addr;
  logic [31:0] wdata;

  logic        error;
  logic        ready;
  logic [31:0] rdata;

  assign valid = reg_req.valid;
  assign write = reg_req.write;
  assign wstrb = reg_req.wstrb;
  assign addr = reg_req.addr;
  assign wdata = reg_req.wdata;

  assign error = reg_rsp.error;
  assign ready = reg_rsp.ready;
  assign rdata = reg_rsp.rdata;

endmodule