`timescale 1ns/1ps

module hsid_fifo #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter FIFO_ADDR_WIDTH = 3 // Address width for FIFO depth
  ) (
    input logic clk,
    input logic rst_n,
    input logic loop_en,
    input logic wr_en,
    input logic rd_en,
    input logic [DATA_WIDTH-1:0] data_in,
    input logic [FIFO_ADDR_WIDTH-1:0] almost_full_threshold, // Element to process
    output logic [DATA_WIDTH-1:0] data_out,
    output logic full,
    output logic almost_full,
    output logic empty,
    input logic clear
  );

  localparam FIFO_DEPTH = 2 ** FIFO_ADDR_WIDTH; // Define FIFO depth based on address width

  // Inicializing FIFO memory
  logic [DATA_WIDTH-1:0] fifo_mem[0:FIFO_DEPTH-1];

  // Initializing read and write pointers
  logic [FIFO_ADDR_WIDTH-1:0] wr_ptr = 0;
  logic [FIFO_ADDR_WIDTH-1:0] rd_ptr = 0;
  logic [FIFO_ADDR_WIDTH:0] fifo_count = 0; // It has to be one bit larger than the address width to count from 0 to FIFO_DEPTH
  logic [1:0] fifo_request;

  // FIFO status signals
  assign full  = (fifo_count == FIFO_DEPTH); // FIFO is full when count reaches depth - 1
  assign empty = (fifo_count == 0);
  assign almost_full = (fifo_count >= almost_full_threshold); // Optional signal for almost full
  // FIFO request: loop has maximum priority (in case it's empty do nothing), then read, write or read and write
  // assign fifo_request = {loop_en && !empty, rd_en && !empty && !loop_en, wr_en && !full && !loop_en}; // 3 bits for read and write enable
  assign fifo_request = {rd_en && !empty, wr_en && !full}; // 2 bits for read and write enable

  // FIFO count update sequentially
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      clear_fifo();
    end else begin
      if (clear) begin
        clear_fifo();
      end else if (loop_en && !empty) begin
        loop_fifo();  // Loop operation, no change in count
      end else if (!loop_en) begin
        casez (fifo_request)
          2'b10:   read_fifo();   // Read operation
          2'b01:   write_input();   // Write operation
          2'b11:   read_and_write();   // Write operation
          default: ;  // No operation or both operations
        endcase
      end
    end
  end

  task loop_fifo();
    data_out <= fifo_mem[rd_ptr];
    fifo_mem[wr_ptr] <= fifo_mem[rd_ptr];
    rd_ptr <= rd_ptr + 1;
    wr_ptr <= wr_ptr + 1;
  endtask

  task read_fifo();
    data_out <= fifo_mem[rd_ptr];
    rd_ptr   <= rd_ptr + 1;
    fifo_count <= fifo_count - 1;
  endtask

  task write_input();
    fifo_mem[wr_ptr] <= data_in;
    wr_ptr <= wr_ptr + 1;
    fifo_count <= fifo_count + 1;
  endtask

  task read_and_write();
    data_out <= fifo_mem[rd_ptr];
    fifo_mem[wr_ptr] <= data_in;
    rd_ptr <= rd_ptr + 1;
    wr_ptr <= wr_ptr + 1;
    fifo_count <= fifo_count; // No change in count
  endtask

  task clear_fifo();
    // Task to clear the FIFO memory and reset pointers
    wr_ptr <= 0;
    rd_ptr <= 0;
    fifo_count <= 0;
    foreach (fifo_mem[i]) begin
      fifo_mem[i] <= '0; // Reset FIFO memory using a for loop
    end
    data_out <= '0; // Reset output data
  endtask

endmodule
