`timescale 1ns / 1ps

import hsid_pkg::*;

class MseGen;

  localparam WORD_WIDTH = HSID_WORD_WIDTH; // Width of the word in bits
  localparam DATA_WIDTH = HSID_DATA_WIDTH; // 16 bits (only 14 bits used)
  localparam DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL; // Data width for multiplication, larger than DATA_WIDTH
  localparam DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC; // Data width for accumulator, larger than DATA_WIDTH
  localparam HSI_BANDS = HSID_HSI_BANDS; // Number of HSI bands
  localparam DATA_PER_WORD = WORD_WIDTH / DATA_WIDTH; // Number of data elements per word
  localparam ELEMENTS = HSI_BANDS / DATA_PER_WORD; // Number of elements in the vector

  rand logic signed [DATA_WIDTH-1:0] vctr1 [HSI_BANDS];
  rand logic signed [DATA_WIDTH-1:0] vctr2 [HSI_BANDS];

  // Generate random vectors
  constraint c_vctrs {
    // foreach (vctr1[i]) vctr1[i] inside {[0:(1 << DATA_WIDTH-2)-1]}; // Use values of 14 bits or less
    // foreach (vctr2[i]) vctr2[i] inside {[0:(1 << DATA_WIDTH-2)-1]};
    foreach (vctr1[i]) vctr1[i] inside {[0:15]}; // Use values of 14 bits or less
    foreach (vctr2[i]) vctr2[i] inside {[0:15]};
  }

  function automatic void fusion_vctr(
      output logic [WORD_WIDTH-1:0] fusion_vctr_1 [ELEMENTS],
      output logic [WORD_WIDTH-1:0] fusion_vctr_2 [ELEMENTS]
    );
    for (int i = 0; i < HSI_BANDS; i+=2) begin
      fusion_vctr_1[i/2] = {vctr1[i], vctr1[i+1]}; // Combine two elements into one word
      fusion_vctr_2[i/2] = {vctr2[i], vctr2[i+1]};
    end
  endfunction

  function automatic void mse(
      output logic [WORD_WIDTH-1:0]   mse
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC-1:0] acc_aux = 0; // Accumulator for the output
    for (int i = 0; i < HSI_BANDS; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
    end
    mse = acc_aux / HSI_BANDS; // Compute mean square error
  endfunction

  function automatic void acc_all(
      output logic [WORD_WIDTH-1:0] acc_int [HSI_BANDS]
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC-1:0] acc_aux = 0; // Accumulator for the output
    for (int i = 0; i < HSI_BANDS; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      acc_int[i] = acc_aux;
    end
  endfunction

endclass