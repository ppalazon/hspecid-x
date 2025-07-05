`timescale 1ns / 1ps

module vctr_fifo_full #(
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter VECTOR_LENGTH = 8  // 8 entries by default
  ) (
    input logic clk,
    input logic rst_n,
    input logic data_in_en,  // Enable signal for input data
    input logic [DATA_WIDTH-1:0] data_in,
    input logic data_out_en,  // Ready signal for output data
    output logic [DATA_WIDTH-1:0] data_out,

    input  logic start,
    output logic done,
    output logic idle,
    output logic ready
  );

  typedef enum logic [2:0] {
    IDLE, READING, OPERATION, DONE
  } state_t;

  // State machine parameters
  state_t current_state = IDLE, next_state = IDLE;

  logic vctr_in_1_full;
  logic vctr_in_2_full;
  logic vctr_in_1_empty;
  logic vctr_in_2_empty;
  logic vctr_out_full;
  logic vctr_out_empty;

  // Operands for vector operations
  logic [DATA_WIDTH-1:0] vctr_in_1_data, vctr_in_2_data, vctr_out_data;
  logic vctr_out_en, compute_en; // Pipeline control signals

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;  // Reset to IDLE state
      vctr_out_data <= 0;
      compute_en <= 0;
    end else begin
      current_state <= next_state;  // Transition to next state
    end
    if (current_state == OPERATION) begin
      // Pipeline the vector operation
      // 1st stage: Read vectors from input FIFOs if they are not empty
      if (!vctr_in_1_empty && !vctr_in_2_empty) begin
        compute_en <= 1;  // Enable computation
      end else begin
        compute_en <= 0;  // Disable computation
      end

      // 2nd stage: Compute the vector operation
      if (compute_en) begin
        vctr_out_data <= vctr_in_1_data + vctr_in_2_data;  // Example operation (addition)
        vctr_out_en <= !vctr_out_full;  // Enable write back operation
      end else begin
        vctr_out_en <= 0;  // Disable write back operation if no data to process
      end
    end else begin
      compute_en <= 0;  // Disable stages
      vctr_out_en <= 0;
    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        idle = 1; ready = 0; done = 0;
        next_state = start ? READING : IDLE;
      end
      READING: begin
        idle = 0; ready = 1; done = 0;
        next_state = vctr_in_1_full && vctr_in_2_full ? OPERATION : READING;
      end
      OPERATION: begin
        idle = 0; ready = 0; done = 0;
        next_state = vctr_out_full && vctr_in_1_empty && vctr_in_2_empty ? DONE : OPERATION;
      end
      DONE: begin
        idle = 0; ready = 0; done = 1;
        next_state = vctr_out_empty ? IDLE : DONE;
      end
      default: begin
        idle = 1; ready = 0; done = 0;
        next_state = IDLE;
      end
    endcase
  end

  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(VECTOR_LENGTH)
  ) vctr_in_1 (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(data_in_en && current_state == READING),
    .rd_en(current_state == OPERATION),
    .data_in(data_in),
    .data_out(vctr_in_1_data),
    .full(vctr_in_1_full),
    .almost_full(),
    .empty(vctr_in_1_empty)
  );

  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(VECTOR_LENGTH)
  ) vctr_in_2 (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(data_in_en && vctr_in_1_full && current_state == READING),
    .rd_en(current_state == OPERATION),
    .data_in(data_in),
    .data_out(vctr_in_2_data),
    .full(vctr_in_2_full),
    .almost_full(),
    .empty(vctr_in_2_empty)
  );

  hsid_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_DEPTH(VECTOR_LENGTH)
  ) vctr_out (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(vctr_out_en),
    .rd_en(current_state == DONE && data_out_en),  // Read enable signal for output FIFO
    .data_in(vctr_out_data),
    .data_out(data_out),
    .full(vctr_out_full),
    .almost_full(),
    .empty(vctr_out_empty)
  );


endmodule
