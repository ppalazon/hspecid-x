`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_x_obi_mem #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    // Obi interface
    // OBI_BUS.Manager obi_manager,
    output hsid_x_obi_inf_pkg::obi_req_t obi_req,
    input hsid_x_obi_inf_pkg::obi_resp_t obi_rsp,

    input logic [WORD_WIDTH-1:0] initial_addr,
    input logic [HSP_LIBRARY_WIDTH-1:0] limit,

    output logic data_out_valid,
    output logic [WORD_WIDTH-1:0] data_out,

    input logic start,
    output logic idle,
    output logic ready,
    output logic done
  );

  typedef enum logic [2:0] {
    IDLE, INIT, READING, DONE
  } hsid_x_obi_mem_state_t;

  hsid_x_obi_mem_state_t current_state = IDLE, next_state = INIT;

  logic [HSP_LIBRARY_WIDTH-1:0] current_limit;
  logic [WORD_WIDTH-1:0] current_addr;
  logic [HSP_LIBRARY_WIDTH:0] requests, reads;

  logic finish_reading;

  assign finish_reading = (requests == current_limit) && (reads == current_limit);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
      current_addr <= '0;
      requests <= '0;
      reads <= '0;
      current_limit <= '1; // Avoid infinite loop
      data_out_valid <= 1'b0;
      data_out <= '0;
      obi_req.req <= '0;
      obi_req.addr <= '0;
      obi_req.we <= 1'b0;
      obi_req.be <= '0;
      obi_req.wdata <= '0;
    end else begin
      current_state <= next_state;
      // If address is valid, make a request to the OBI subordinate
      if (current_state == INIT) begin
        current_addr <= initial_addr;
        current_limit <= limit == 0 ? 1 : limit; // Avoid setting limit to 0 to prevent infinite loop
        requests <= '0;
        reads <= '0;
        obi_req.req <= 1'b0;
      end
      else if (current_state == READING) begin
        obi_req.req <= 1'b1;
        if (obi_rsp.gnt && requests < current_limit) begin
          obi_req.addr <= current_addr;
          obi_req.we <= 1'b0;
          obi_req.be <= 4'b1111;
          obi_req.wdata <= '0;
          current_addr <= current_addr + WORD_WIDTH / 8; // Increment address by word size
          requests <= requests + 1;
        end
        if (obi_rsp.rvalid && reads < current_limit) begin
          data_out_valid <= 1'b1;
          data_out <= obi_rsp.rdata;
          reads <= reads + 1;
        end else begin
          data_out_valid <= 1'b0;
        end
        if (finish_reading) begin
          obi_req.req <= 1'b0; // No more requests after reading all data
        end
      end

    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        idle = 1; ready = 0; done = 0;
        next_state = start ? INIT : IDLE;
      end
      INIT: begin
        idle = 0; ready = 1; done = 0;
        next_state = READING;
      end
      READING: begin
        idle = 0; ready = 1; done = 0;
        next_state = finish_reading ? DONE : READING;
      end
      DONE: begin
        idle = 0; ready = 0; done = 1;
        next_state = IDLE;
      end
      default: begin
        idle = 1; ready = 0; done = 0;
        next_state = IDLE;
      end
    endcase
  end

endmodule