`timescale 1ns / 1ps

import hsid_pkg::*;

class SqDfAccGen;

  localparam DATA_WIDTH = HSID_DATA_WIDTH; // 16 bits (only 14 bits used)
  localparam DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL; // Data width for multiplication, larger than DATA_WIDTH
  localparam DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC; // Data width for accumulator, larger than DATA_WIDTH
  localparam VECTOR_LENGTH = HSID_VECTOR_LENGTH_TB; // Length of the vector

  rand logic signed [DATA_WIDTH-1:0] vctr1 [VECTOR_LENGTH];
  rand logic signed [DATA_WIDTH-1:0] vctr2 [VECTOR_LENGTH];
  rand logic [DATA_WIDTH_ACC-1:0] initial_acc; // Initial accumulator value

  // Generate random vectors
  constraint c_vctrs {
    // foreach (vctr1[i]) vctr1[i] inside {[0:(1 << DATA_WIDTH-2)-1]}; // Use values of 14 bits or less
    // foreach (vctr2[i]) vctr2[i] inside {[0:(1 << DATA_WIDTH-2)-1]};
    foreach (vctr1[i]) vctr1[i] inside {[0:99]}; // Use values of 14 bits or less
    foreach (vctr2[i]) vctr2[i] inside {[0:99]};
    initial_acc inside {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}; // Initial accumulator can be small values
  }

  function automatic void sq_df_acc_vctr(
      output logic [DATA_WIDTH_ACC-1:0]   acc [VECTOR_LENGTH] // wider to hold overflow
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC-1:0] acc_aux = initial_acc; // Accumulator for the output
    for (int i = 0; i < VECTOR_LENGTH; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      acc[i] = acc_aux; // Store the accumulated value
    end
  endfunction

endclass