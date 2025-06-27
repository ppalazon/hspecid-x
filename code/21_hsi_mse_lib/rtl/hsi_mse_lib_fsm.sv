`timescale 1ns / 1ps

typedef enum logic [2:0] {
  IDLE, READ_MEASURE, COMPUTE_MSE, WAIT_MSE, COMPARE_MSE, DONE
} hsi_mse_lib_state_t;

module hsi_mse_lib_fsm #(
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter ELEMENTS = HSI_BANDS / 2,  // Number of elements in the vector
    parameter ELEMENTS_ADDR = $clog2(ELEMENTS),  // Address width for HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    parameter HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)  // Number of bits to represent vector length
  ) (
    input logic clk,
    input logic rst_n,

    // Library size input
    input logic [HSI_LIBRARY_SIZE_ADDR:0] hsi_library_size,  // Length of the vectors

    // Fifo status signals
    input logic fifo_measure_full,  // Full signal for measure vector FIFO
    input logic fifo_measure_empty,  // Empty signal for measure vector FIFO
    input logic fifo_ref_empty,  // Empty signal for output data FIFO
    input logic fifo_ref_full,  // Full signal for output data FIFO

    // MSE signals
    input logic msi_valid,
    input logic msi_comparison_valid,

    // Current state
    output hsi_mse_lib_state_t state,
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] vctr_count,
    output logic element_start,  // Start vector processing signal
    output logic element_last,  // Last vector processing signal
    output logic element_valid,  // Element valid signal
    output logic vctr_last,
    output logic fifo_both_read_en,

    // Block interface for handshake signals
    input logic start,
    output logic done,
    output logic idle,
    output logic ready
  );

  // Assigns statements
  logic [ELEMENTS_ADDR-1:0] element_count;
  assign fifo_both_read_en = (state == COMPUTE_MSE && !fifo_ref_empty && !fifo_measure_empty);
  // assign element_last = (element_count == ELEMENTS - 1);
  // assign element_start = (element_count == 0); // && fifo_both_read_en
  assign vctr_last = (vctr_count == hsi_library_size - 1);

  hsi_mse_lib_state_t current_state = IDLE, next_state = READ_MEASURE;

  assign state = current_state;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;  // Reset to IDLE state
      element_count <= 0;  // Reset element count
      vctr_count <= 0;  // Reset vector count
      element_start <= 0;  // Reset start signal
      element_last <= 0;  // Reset last signal
      element_valid <= 0;  // Reset valid signal
    end else begin
      current_state <= next_state;  // Transition to next state
    end
    element_start <= (element_count == 0 && fifo_both_read_en);
    element_last <= (element_count == ELEMENTS - 1);
    element_valid <= fifo_both_read_en;
    if (fifo_both_read_en) begin
      element_count <= element_count + 1;
      if (element_last) begin
        vctr_count <= vctr_count + 1;
      end
    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        idle = 1; ready = 0; done = 0;
        next_state = start ? READ_MEASURE : IDLE;
      end
      READ_MEASURE: begin
        idle = 0; ready = 1; done = 0;
        next_state = fifo_measure_full ? COMPUTE_MSE : READ_MEASURE;
      end
      COMPUTE_MSE: begin
        idle = 0; ready = !fifo_ref_full; done = 0;
        next_state = (vctr_last & element_last) ? WAIT_MSE : COMPUTE_MSE;
      end
      WAIT_MSE: begin
        idle = 0; ready = 0; done = 0;
        next_state = msi_valid ? COMPARE_MSE : WAIT_MSE;
      end
      COMPARE_MSE: begin
        idle = 0; ready = 0; done = 0;
        next_state = msi_comparison_valid ? DONE : COMPARE_MSE;
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