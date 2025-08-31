`timescale 1ns / 1ps

import hsid_pkg::*;

/*
 @WAVEDROM_START
 { signal: [
 { name: "clk",            wave: "p................." },
 { name: "initial_addr",   wave: "x.3x..............", data: ['0x20'] },
 { name: "limit",          wave: "x.4x..............", data: ['4'] },
 { name: "data_out_valid", wave: "l................." },
 { name: "data_out",       wave: "l................." },
 { name: "start",          wave: "lhl..............." },
 { name: "idle",           wave: "hl...............h" },
 { name: "ready",          wave: "l..h............l." },
 { name: "done",           wave: "l...............hl" },
 { name: "obi_req.req",    wave: "l..h........l....." },
 { name: "obi_req.we",     wave: "l................." },
 { name: "obi_req.be",     wave: "8.................", data: ['0xF'] },
 { name: "obi_req.addr",   wave: "x..3.33....3.x....", data: ['0x20', '0x24', '0x28', '0x2C'] },
 { name: "obi_req.wdata",  wave: "9.................", data: ['0x0'] },
 { name: "obi_rsp.gnt",    wave: "l...h.l...hlhl...." },
 { name: "obi_rsp.rvalid", wave: "l...h.l....hl..hl." },
 { name: "obi_rsp.rdata",  wave: "x...44x....4x..4x.", data: ['0x1', '0x2', '0x3', '0x4'] }
 ]}
 @WAVEDROM_END
 */
module hsid_x_obi_mem #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter MEM_ACCESS_WIDTH = HSID_MEM_ACCESS_WIDTH  // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    // Obi interface
    // OBI_BUS.Manager obi_manager,
    output var hsid_x_obi_inf_pkg::obi_req_t obi_req,
    input wire hsid_x_obi_inf_pkg::obi_resp_t obi_rsp,

    input logic [WORD_WIDTH-1:0] initial_addr,
    input logic [MEM_ACCESS_WIDTH-1:0] limit,

    output logic data_out_valid,
    output logic [WORD_WIDTH-1:0] data_out,

    input logic start,
    input logic clear,
    output logic idle,
    output logic ready,
    output logic done
  );

  hsid_x_obi_mem_state_t current_state = HXOM_IDLE, next_state = HXOM_INIT;

  logic [MEM_ACCESS_WIDTH-1:0] current_limit;
  // logic [WORD_WIDTH-1:0] current_addr;
  logic [MEM_ACCESS_WIDTH:0] requests, reads;

  logic finish_requesting;
  logic finish_reading;

  // Continuous assignments for output signals
  assign finish_requesting = (requests >= current_limit);
  assign finish_reading = (reads >= current_limit);


  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= HXOM_IDLE;
      reset_values();
    end else begin
      current_state <= next_state;
      if (current_state == HXOM_CLEAR) begin
        reset_values();
      end else if (current_state == HXOM_INIT) begin
        // current_addr <= initial_addr;
        obi_req.addr <= initial_addr;
        obi_req.we <= 1'b0;
        obi_req.be <= 4'b1111;
        obi_req.wdata <= '0;
        current_limit <= limit == 0 ? '1 : limit; // Avoid setting limit to 0 to prevent infinite loop
        requests <= '0;
        reads <= '0;
      end else if (current_state == HXOM_READING) begin
        obi_req.req <= !finish_requesting; // Request more data until limit is reached
        if (obi_req.req && obi_rsp.gnt) begin
          obi_req.addr <= obi_req.addr + WORD_WIDTH / 8; // Increment address by word size
          requests <= requests + 1;
        end
        if (obi_rsp.rvalid && !finish_reading) begin
          data_out_valid <= 1'b1;
          data_out <= obi_rsp.rdata;
          reads <= reads + 1;
        end else begin
          data_out_valid <= 1'b0;
        end
        // if (finish_requesting) begin
        //   obi_req.req <= 1'b0; // No more requests after reading all data
        // end
      end

    end
  end

  always_comb begin
    case (current_state)
      HXOM_IDLE: begin
        idle = 1; ready = 0; done = 0;
        next_state = !clear && start ? HXOM_INIT : HXOM_IDLE;
      end
      HXOM_INIT: begin
        idle = 0; ready = 0; done = 0;
        next_state = clear ? HXOM_CLEAR : HXOM_READING;
      end
      HXOM_READING: begin
        idle = 0; ready = 1; done = 0;
        next_state = clear ? HXOM_CLEAR : (finish_reading ? HXOM_DONE : HXOM_READING);
      end
      HXOM_DONE: begin
        idle = 0; ready = 0; done = 1;
        next_state = HXOM_IDLE;
      end
      HXOM_CLEAR: begin
        idle = 0; ready = 0; done = 0;
        next_state = HXOM_IDLE;
      end
      default: begin
        idle = 1; ready = 0; done = 0;
        next_state = HXOM_IDLE;
      end
    endcase
  end

  task reset_values();
// current_addr <= '0;
    requests <= '0;
    reads <= '0;
    current_limit <= '0; // Avoid infinite loop
    data_out_valid <= 1'b0;
    data_out <= '0;
    obi_req.req <= '0;
    obi_req.addr <= '0;
    obi_req.we <= 1'b0;
    obi_req.be <= '0;
    obi_req.wdata <= '0;
  endtask

endmodule