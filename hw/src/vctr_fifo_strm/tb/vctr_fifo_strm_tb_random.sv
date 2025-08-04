`timescale 1ns / 1ps

import hsid_pkg::*;

class VctrFifoStreamGen#(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH,
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH
  );

  localparam int VECTOR_LENGTH = 2 ** HSP_BANDS_WIDTH;

  rand logic [WORD_WIDTH-1:0] vctr1 [VECTOR_LENGTH];
  rand logic [WORD_WIDTH-1:0] vctr2 [VECTOR_LENGTH];

  // Generate random vectors
  constraint c_vctrs {
    foreach (vctr1[i]) vctr1[i] inside {[0:(1 << WORD_WIDTH)-1]};
    foreach (vctr2[i]) vctr2[i] inside {[0:(1 << WORD_WIDTH)-1]};
  }

  function automatic void sum_vctr(
      output logic [WORD_WIDTH-1:0] sum [VECTOR_LENGTH] // wider to hold overflow
    );
    for (int i = 0; i < VECTOR_LENGTH; i++) begin
      sum[i] = vctr1[i] + vctr2[i];
    end
  endfunction

endclass