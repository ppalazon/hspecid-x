`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_divider #(
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter K = 32, // Number of bits for quotient and remainder
    localparam DK = 2*K // Number of bits for dividend
  ) (
    input logic clk,
    input logic rst_n,
    input logic clear,
    input logic start,
    input logic [DK-1:0] dividend,
    input logic [K-1:0] divisor,
    input logic of_in, // Dividend or divisor is overflowed
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_in,
    output logic idle,
    output logic done,
    output logic ready,
    output logic [K-1:0] quotient,
    output logic [K-1:0] remainder,
    output logic overflow,
    output logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_out
  );

  localparam STEP_COUNT_WIDTH = $clog2(K);

  // State machine states
  hsid_ite_div_state_t state = HID_IDLE, next_state = HID_IDLE;

  logic [K:0] divisor_ext;
  logic [K:0] rem_reg; // One bit wider to handle MSB flag
  logic [K-1:0] q_reg; // Shift dividend register from LSB to MSB
  logic qbit_next;
  logic [K:0] rem_shift, rem_next, rem_final;
  logic [STEP_COUNT_WIDTH-1:0] step; // Step counter

  assign rem_shift = {rem_reg[K-1:0], q_reg[K-1]}; // Shift left remainder and bring in next bit of dividend
  assign rem_next = rem_reg[K] ? (rem_shift + divisor_ext) : (rem_shift - divisor_ext); // Add or subtract divisor based on MSB of remainder
  assign qbit_next = ~rem_next[K]; // Quotient bit is 1 if MSB of remainder is 0
  assign rem_final = (state == HID_CHECK) ? (rem_reg[K] ? (rem_reg + divisor_ext) : rem_reg) : '0;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= HID_IDLE;
      reset_dut();
    end else begin
      state <= next_state;
      case (state)
        HID_CLEAR: begin
          reset_dut();
        end
        HID_IDLE: begin
          if (clear) begin
            reset_dut();
          end else if (start) begin
            // In this point we're always computing step 0
            divisor_ext <= {1'b0, divisor}; // Align divisor with dividend
            rem_reg <= {1'b0, dividend[DK-1:K]}; // MSB part of dividend
            q_reg <= dividend[K-1:0];            // LSB part of dividend
            step <= K - 1;
            overflow <= of_in || (dividend >= {{K{1'b0}}, divisor} << K); // Check for overflow condition, we don't have to check for divisor == 0 here
            hsp_ref_out <= hsp_ref_in; // Pass through HSP reference
          end
        end
        HID_COMPUTE: begin
          rem_reg <= rem_next; // Update remainder
          q_reg <= {q_reg[K-2:0], qbit_next}; // Set quotient bit
          step <= step - 1; // Decrement step counter
        end
        HID_CHECK: begin
          quotient <= q_reg;
          remainder <= rem_final[K-1:0];
        end
      endcase
    end
  end

  always_comb begin
    case (state)
      HID_IDLE: begin
        idle = 1; ready = 1; done = 0;
        next_state = start && !clear ? HID_COMPUTE : HID_IDLE;
      end
      HID_COMPUTE: begin
        idle = 0; ready = 0; done = 0;
        next_state = clear ? HID_CLEAR : (overflow ? HID_DONE : (step == 0 ? HID_CHECK : HID_COMPUTE));
      end
      HID_CHECK: begin
        idle = 0; ready = 0; done = 0;
        next_state = clear ? HID_CLEAR : HID_DONE;
      end
      HID_DONE: begin
        idle = 0; ready = 0; done = 1;
        next_state = HID_IDLE;
      end
      HID_CLEAR: begin
        idle = 0; ready = 0; done = 0;
        next_state = HID_IDLE;
      end
      default: begin
        idle = 1; ready = 0; done = 0;
        next_state = HID_IDLE;
      end
    endcase
  end

  task reset_dut();
    divisor_ext <= 0;
    q_reg <= 0;
    rem_reg <= 0;
    step <= 0;
    overflow <= 0;
    quotient <= 0;
    remainder <= 0;
    hsp_ref_out <= 0;
  endtask

endmodule