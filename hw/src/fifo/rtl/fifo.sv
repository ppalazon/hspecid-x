`timescale 1ns/1ps

/*
 @WAVEDROM_START
 { signal: [
 { name: "clk",      wave: "P........." },
 { name: "rst_n",    wave: "L........." },
 { name: "wr_en",    wave: "L........." },
 { name: "rd_en",    wave: "L........." },
 { name: "data_in",  wave: "L........." },
 { name: "data_out", wave: "L........." },
 { name: "full",     wave: "L........." },
 { name: "empty",    wave: "L........." },
 ]}
 @WAVEDROM_END
 */
module fifo #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter FIFO_DEPTH = 8,  // 8 entries by default
    parameter FIFO_ALMOST_FULL_THRESHOLD = FIFO_DEPTH - 1, // Optional threshold for almost full
    localparam FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH) // Address width for FIFO depth
  ) (
    input logic clk,
    input logic rst_n,
    input logic wr_en,
    input logic rd_en,
    input logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic full,
    output logic almost_full,
    output logic empty
  );

  // Inicializing FIFO memory
  logic [DATA_WIDTH-1:0] fifo_mem[0:FIFO_DEPTH-1];

  // Initializing read and write pointers
  logic [FIFO_ADDR_WIDTH-1:0] wr_ptr = 0;
  logic [FIFO_ADDR_WIDTH-1:0] rd_ptr = 0;
  logic [FIFO_ADDR_WIDTH:0] fifo_count = 0; // It has to be one bit larger than the address width to count from 0 to FIFO_DEPTH

  // FIFO status signals
  assign full  = (fifo_count == FIFO_DEPTH); // FIFO is full when count reaches depth - 1
  assign empty = (fifo_count == 0);
  assign almost_full = (fifo_count >= FIFO_ALMOST_FULL_THRESHOLD); // Optional signal for almost full

  // FIFO count update sequentially
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fifo_count <= 0; // Reset FIFO count
    end else begin
      case ({
            rd_en && !empty, wr_en && !full  // 2 bits for read and write enable
          })
        2'b10:   fifo_count <= fifo_count - 1;  // Read operation
        2'b01:   fifo_count <= fifo_count + 1;  // Write operation
        default: fifo_count <= fifo_count;  // No operation or both operations
      endcase
    end
  end

  // FIFO write operation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr <= 0;
      for (int i = 0; i < FIFO_DEPTH; i++) begin // Reset FIFO memory using a for loop
        fifo_mem[i] <= '0;
      end
    end else if (wr_en && !full) begin
      fifo_mem[wr_ptr] <= data_in;
      wr_ptr <= wr_ptr + 1;
    end
  end

  // FIFO read operation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr <= 0; // Reset read pointer
      data_out <= '0;  // Reset output data
    end else if (rd_en && !empty) begin
      data_out <= fifo_mem[rd_ptr];
      rd_ptr   <= rd_ptr + 1;
    end
  end

endmodule
