`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidMainGen #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits (only 14 bits used)
    parameter int DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter int DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter int TEST_BANDS = HSID_TEST_BANDS, // Number of HSI bands
    parameter int TEST_LIBRARY_SIZE = HSID_TEST_LIBRARY_SIZE // Size of the HSI library
  );

  localparam TEST_LIBRARY_SIZE_ADDR = $clog2(TEST_LIBRARY_SIZE);
  localparam DATA_PER_WORD = WORD_WIDTH / DATA_WIDTH; // Number of data elements per word
  localparam TEST_ELEMENTS = TEST_BANDS / DATA_PER_WORD; // Number of elements in the vector

  rand logic [DATA_WIDTH-1:0] measure [TEST_BANDS];

  // Generate random vectors
  constraint c_vctrs {
    // foreach (measure[i]) measure[i] inside {[0:(1 << DATA_WIDTH-2)-1]}; // Use values of 14 bits or less
    foreach (measure[i]) measure[i] inside {[0:9]}; // Use values of 14 bits or less
  }

  function automatic void fusion_vctr(
      input logic [DATA_WIDTH-1:0] vctr [TEST_BANDS],
      output logic [WORD_WIDTH-1:0] fusion_vctr [TEST_ELEMENTS]
    );
    for (int i = 0; i < TEST_BANDS; i+=2) begin
      fusion_vctr[i/2] = {vctr[i], vctr[i+1]};
    end
  endfunction

  function automatic void mse(
      input logic [DATA_WIDTH-1:0] vctr1 [TEST_BANDS],
      input logic [DATA_WIDTH-1:0] vctr2 [TEST_BANDS],
      output logic [WORD_WIDTH-1:0]   mse
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC-1:0] acc_aux = 0; // Accumulator for the output
    for (int i = 0; i < TEST_BANDS; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      // $display("Band %0d: vctr1 = %0d, vctr2 = %0d, diff = %0d, mult = %0d, acc_aux = %0d",
      //   i, vctr1[i], vctr2[i], diff, mult, acc_aux);
    end

    mse = acc_aux  / TEST_BANDS; // Compute mean square error
  endfunction

  function automatic void acc_all(
      input logic [DATA_WIDTH-1:0] vctr1 [TEST_BANDS],
      input logic [DATA_WIDTH-1:0] vctr2 [TEST_BANDS],
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

  function automatic void min_max_mse(
      logic [WORD_WIDTH-1:0] expected_mse [TEST_LIBRARY_SIZE],
      output logic [WORD_WIDTH-1:0] min_mse_value,
      output logic [WORD_WIDTH-1:0] max_mse_value,
      output logic [TEST_LIBRARY_SIZE_ADDR-1:0] min_mse_ref,
      output logic [TEST_LIBRARY_SIZE_ADDR-1:0] max_mse_ref
    );
    logic [WORD_WIDTH-1:0] aux_min_mse_value = (1 << WORD_WIDTH) - 1; // Initialize to max value
    logic [WORD_WIDTH-1:0] aux_max_mse_value = '0; // Initialize to min value
    for (int i = 0; i < TEST_LIBRARY_SIZE; i++) begin
      if (expected_mse[i] <= aux_min_mse_value) begin
        aux_min_mse_value = expected_mse[i];
        min_mse_ref = i; // Update reference for minimum MSE
      end
      if (expected_mse[i] >= aux_max_mse_value) begin
        aux_max_mse_value = expected_mse[i];
        max_mse_ref = i; // Update reference for maximum MSE
      end
    end
    min_mse_value = aux_min_mse_value; // Set minimum MSE value
    max_mse_value = aux_max_mse_value; // Set maximum MSE value

  endfunction

endclass