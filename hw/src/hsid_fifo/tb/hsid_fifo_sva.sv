`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_fifo_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // 16 bits by default
    parameter FIFO_ADDR_WIDTH = HSID_FIFO_ADDR_WIDTH, // Address width for FIFO depth
    localparam FIFO_DEPTH = 2 ** FIFO_ADDR_WIDTH
  ) (
    input logic clk,
    input logic rst_n,
    input logic loop_en,
    input logic wr_en,
    input logic rd_en,
    input logic [WORD_WIDTH-1:0] data_in,
    input logic [FIFO_ADDR_WIDTH-1:0] almost_full_threshold, // Element to process
    input logic [WORD_WIDTH-1:0] data_out,
    input logic full,
    input logic almost_full,
    input logic empty,
    input logic clear,

    // Internal signals
    input logic [WORD_WIDTH-1:0] fifo_mem[0:FIFO_DEPTH-1],

    // Initializing read and write pointers
    input logic [FIFO_ADDR_WIDTH-1:0] wr_ptr = 0,
    input logic [FIFO_ADDR_WIDTH-1:0] rd_ptr = 0,
    input logic [FIFO_ADDR_WIDTH:0] fifo_count = 0, // It has to be one bit larger than the address width to count from 0 to FIFO_DEPTH
    input logic [1:0] fifo_request
  );

  localparam MAX_PTR_VALUE = FIFO_DEPTH - 1;

  // Assert fifo full condition
  property activate_fifo_full;
    @(posedge clk) disable iff (!rst_n) full |-> (fifo_count == FIFO_DEPTH);
  endproperty

  assert property (activate_fifo_full) else $error("FIFO is full when it should not be");
  cover property (activate_fifo_full); // $display("Checked: FIFO is full");

  // Assert fifo almost full condition
  property activate_fifo_almost_full;
    @(posedge clk) disable iff (!rst_n) almost_full |-> (fifo_count >= almost_full_threshold);
  endproperty

  assert property (activate_fifo_almost_full) else $error("FIFO is almost full when it should not be");
  cover property (activate_fifo_almost_full); //$display("Checked: FIFO is almost full");

  // Assert fifo empty condition
  property activate_fifo_empty;
    @(posedge clk) disable iff (!rst_n) empty |-> (fifo_count == 0);
  endproperty
  assert property (activate_fifo_empty) else $error("FIFO is empty when it should not be");
  cover property (activate_fifo_empty); // $display("Checked: FIFO is empty");

  // Assert values next cycle when clear is set
  property initialize_on_clear;
    @(posedge clk) disable iff (!rst_n) clear |=> (fifo_count == 0 && wr_ptr == 0 && rd_ptr == 0);
  endproperty
  assert property (initialize_on_clear) else $error("FIFO is not cleared properly");
  cover property (initialize_on_clear); //$display("Checked: FIFO is cleared");

  // Assert loop operation on data_out and mem_fifo
  property data_on_loop;
    @(posedge clk) disable iff (!rst_n) loop_en && !empty && !clear |-> ##1
      fifo_count == $past(fifo_count) && data_out == fifo_mem[$past(rd_ptr)] && fifo_mem[$past(wr_ptr)] == fifo_mem[$past(rd_ptr)];
  endproperty
  assert property (data_on_loop) else $error("FIFO data_out on loop operation is not correct");
  cover property (data_on_loop); //$display("Checked: FIFO data_out on loop operation is not correct");

  // Assert read operation on data_out and rd_ptr
  property ptr_data_on_read;
    @(posedge clk) disable iff (!rst_n) rd_en && !empty && !clear && !loop_en |-> ##1
      data_out == fifo_mem[$past(rd_ptr)] && rd_ptr == (($past(rd_ptr) + 1) & MAX_PTR_VALUE);
  endproperty

  assert property (ptr_data_on_read) else $error("FIFO on read operation is not correct: data_out = %0h, rd_ptr = %0h -> %0h / %0h", data_out, $past(rd_ptr), $past(rd_ptr)+1, rd_ptr);
  cover property (ptr_data_on_read); // $display("Checked: FIFO data_out and rd_ptr on read operation");

  // Assert write operation on data_in and wr_ptr
  property ptr_data_on_write;
    @(posedge clk) disable iff (!rst_n) wr_en && !full && !clear && !loop_en |-> ##1
      fifo_mem[$past(wr_ptr)] == $past(data_in) && wr_ptr == (($past(wr_ptr) + 1) & MAX_PTR_VALUE);
  endproperty

  assert property (ptr_data_on_write) else $error("FIFO on write operation is not correct: data_in = %0h, wr_ptr = %0h -> %0h / %0h", data_in, $past(wr_ptr), $past(wr_ptr)+1, wr_ptr);
  cover property (ptr_data_on_write); // $display("Checked: FIFO data_in and wr_ptr on write operation");

endmodule