`timescale 1ns / 1ps

module hsid_fifo_abv #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter FIFO_ADDR_WIDTH = 4, // Address width for FIFO depth
    localparam FIFO_DEPTH = 2 ** FIFO_ADDR_WIDTH
  ) (
    input logic clk,
    input logic rst_n,
    input logic loop_en,
    input logic wr_en,
    input logic rd_en,
    input logic [DATA_WIDTH-1:0] data_in,
    input logic [FIFO_ADDR_WIDTH-1:0] almost_full_threshold, // Element to process
    input logic [DATA_WIDTH-1:0] data_out,
    input logic full,
    input logic almost_full,
    input logic empty,
    input logic clear,

    // Internal signals
    input logic [DATA_WIDTH-1:0] fifo_mem[0:FIFO_DEPTH-1],

    // Initializing read and write pointers
    input logic [FIFO_ADDR_WIDTH-1:0] wr_ptr = 0,
    input logic [FIFO_ADDR_WIDTH-1:0] rd_ptr = 0,
    input logic [FIFO_ADDR_WIDTH:0] fifo_count = 0, // It has to be one bit larger than the address width to count from 0 to FIFO_DEPTH
    input logic [2:0] fifo_request
  );

  // Assert fifo full condition
  property fifo_full;
    @(posedge clk) disable iff (!rst_n) full |-> (fifo_count == FIFO_DEPTH);
  endproperty

  assert property (fifo_full) else $error("FIFO is full when it should not be");
  cover property (fifo_full); // $display("Checked: FIFO is full");

  // Assert fifo almost full condition
  property fifo_almost_full;
    @(posedge clk) disable iff (!rst_n) almost_full |-> (fifo_count >= almost_full_threshold);
  endproperty

  assert property (fifo_almost_full) else $error("FIFO is almost full when it should not be");
  cover property (fifo_almost_full); //$display("Checked: FIFO is almost full");

  // Assert fifo empty condition
  property fifo_empty;
    @(posedge clk) disable iff (!rst_n) empty |-> (fifo_count == 0);
  endproperty
  assert property (fifo_empty) else $error("FIFO is empty when it should not be");
  cover property (fifo_empty); // $display("Checked: FIFO is empty");

  // Assert values next cycle when clear is set
  property fifo_after_clear;
    @(posedge clk) disable iff (!rst_n) clear |=> (fifo_count == 0 && wr_ptr == 0 && rd_ptr == 0);
  endproperty
  assert property (fifo_after_clear) else $error("FIFO is not cleared properly");
  cover property (fifo_after_clear); //$display("Checked: FIFO is cleared");

  // Assert loop operation on data_out and mem_fifo
  property fifo_after_loop;
    @(posedge clk) disable iff (!rst_n) loop_en && !empty && !clear |=>
      fifo_count == $past(fifo_count) && data_out == fifo_mem[$past(rd_ptr)] && fifo_mem[$past(wr_ptr)] == fifo_mem[$past(rd_ptr)];
  endproperty
  assert property (fifo_after_loop) else $error("FIFO data_out on loop operation is not correct");
  cover property (fifo_after_loop); //$display("Checked: FIFO data_out on loop operation is not correct");

endmodule