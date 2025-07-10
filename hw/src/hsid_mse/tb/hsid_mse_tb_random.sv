`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidMseGen#(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits (only 14 bits used)
    parameter int DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter int DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter int TEST_BANDS = HSID_TEST_BANDS, // Number of HSI bands
    parameter int TEST_LIBRARY_SIZE = HSID_TEST_LIBRARY_SIZE, // Size of the HSI library
    parameter int TEST_ELEMENTS = TEST_BANDS / 2 // Number of elements in the vector
  );

  rand logic signed [DATA_WIDTH-1:0] vctr1 [TEST_BANDS];
  rand logic signed [DATA_WIDTH-1:0] vctr2 [TEST_BANDS];

  // Generate random vectors
  constraint c_vctrs {
    // foreach (vctr1[i]) vctr1[i] inside {[0:(1 << DATA_WIDTH-2)-1]}; // Use values of 14 bits or less
    // foreach (vctr2[i]) vctr2[i] inside {[0:(1 << DATA_WIDTH-2)-1]};
    foreach (vctr1[i]) vctr1[i] inside {[0:15]}; // Use values of 14 bits or less
    foreach (vctr2[i]) vctr2[i] inside {[0:15]};
  }

  function automatic void fusion_vctr(
      output logic [WORD_WIDTH-1:0] fusion_vctr_1 [TEST_ELEMENTS],
      output logic [WORD_WIDTH-1:0] fusion_vctr_2 [TEST_ELEMENTS]
    );
    for (int i = 0; i < TEST_BANDS; i+=2) begin
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
    for (int i = 0; i < TEST_BANDS; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
    end
    mse = acc_aux / TEST_BANDS; // Compute mean square error
  endfunction

  function automatic void acc_all(
      output logic [WORD_WIDTH-1:0] acc_int [TEST_BANDS]
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC-1:0] acc_aux = 0; // Accumulator for the output
    for (int i = 0; i < TEST_BANDS; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      acc_int[i] = acc_aux;
    end
  endfunction

endclass