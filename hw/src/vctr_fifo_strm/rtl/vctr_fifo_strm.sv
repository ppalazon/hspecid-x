`timescale 1ns / 1ps

module vctr_fifo_strm #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter LENGTH_BITS = 10,  // Number of bits to represent vector length
    parameter BUFFER_LENGTH = 4  // 8 entries by default
  ) (
    input logic clk,
    input logic rst_n,

    input logic data_in_v1_en,  // Enable input data for vector 1
    input logic [DATA_WIDTH-1:0] data_in_v1,
    output logic data_in_v1_full,  // Full signal for vector 1 input FIFO

    input logic data_in_v2_en,  // Enable input data for vector 2
    input logic [DATA_WIDTH-1:0] data_in_v2,
    output logic data_in_v2_full,  // Full signal for vector 2 input FIFO

    input logic data_out_en,  // Ready signal for output data
    output logic [DATA_WIDTH-1:0] data_out,
    output logic data_out_empty,  // Empty signal for output FIFO

    input logic [LENGTH_BITS-1:0] vector_length,  // Length of the vectors

    input  logic start,
    output logic done,
    output logic idle,
    output logic ready
  );

  typedef enum logic [1:0] {
    IDLE, COMPUTE, DONE
  } state_t;
  // State machine parameters
  state_t current_state = IDLE, next_state = COMPUTE;

  logic vctr_in_1_empty;
  logic vctr_in_2_empty;
  logic vctr_out_full;
  logic vctr_out_almost_full;

  // Operands for vector operations
  logic [DATA_WIDTH-1:0] read_v1_data, read_v2_data, vctr_out_data;
  logic vctr_out_en, compute_en; // Pipeline control signals
  logic [LENGTH_BITS-1:0] processed;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;  // Reset to IDLE state
      vctr_out_data <= 0;
      compute_en <= 0;
      processed <= 0;
    end else begin
      current_state <= next_state;  // Transition to next state
    end
    if (current_state == COMPUTE) begin // Pipeline the vector operation

      // 1st stage: Read to read vectors from input FIFOs if they are not empty
      if (!vctr_in_1_empty && !vctr_in_2_empty) begin
        compute_en <= 1;  // Enable computation
      end else begin
        compute_en <= 0;  // Disable computation
      end

      // 2nd stage: Compute the vector operation
      if (compute_en) begin
        vctr_out_data <= read_v1_data + read_v2_data;  // Example operation (addition)
        vctr_out_en <= !vctr_out_full;
        processed <= processed + 1; // Increment processed count
      end else begin
        vctr_out_en <= 0;
      end
    end else begin  // Disable stages
      compute_en <= 0;
      vctr_out_en <= 0;
    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        idle = 1; ready = 0; done = 0;
        next_state = start ? COMPUTE : IDLE;
      end
      COMPUTE: begin
        idle = 0; ready = 1; done = 0;
        next_state = vector_length == processed ? DONE : COMPUTE;
      end
      DONE: begin
        idle = 0; ready = 0; done = 1;
        next_state = data_out_empty ? IDLE : DONE;
      end
      default: begin
        idle = 1; ready = 0; done = 0;
        next_state = IDLE;
      end
    endcase
  end

  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(BUFFER_LENGTH)
  ) vctr_in_1 (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(current_state == COMPUTE && data_in_v1_en && !vctr_out_almost_full),
    .rd_en(current_state == COMPUTE && !vctr_in_1_empty && !vctr_in_2_empty),
    .data_in(data_in_v1),
    .data_out(read_v1_data),
    .full(data_in_v1_full),
    .almost_full(),
    .empty(vctr_in_1_empty)
  );

  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(BUFFER_LENGTH)
  ) vctr_in_2 (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(current_state == COMPUTE && data_in_v2_en && !vctr_out_almost_full),
    .rd_en(current_state == COMPUTE && !vctr_in_1_empty && !vctr_in_2_empty),
    .data_in(data_in_v2),
    .data_out(read_v2_data),
    .full(data_in_v2_full),
    .almost_full(),
    .empty(vctr_in_2_empty)
  );

  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(BUFFER_LENGTH),
    .FIFO_ALMOST_FULL_THRESHOLD(BUFFER_LENGTH - 2)  // Almost full threshold taking account of pipeline stages
  ) vctr_out (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(vctr_out_en),
    .rd_en(current_state != IDLE && data_out_en),
    .data_in(vctr_out_data),
    .data_out(data_out),
    .full(vctr_out_full),
    .almost_full(vctr_out_almost_full),
    .empty(data_out_empty)
  );


endmodule
