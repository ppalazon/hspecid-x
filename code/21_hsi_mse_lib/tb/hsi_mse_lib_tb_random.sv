`timescale 1ns / 1ps

import hsi_mse_pkg::*;

class HsiMseLibGen;

  localparam WORD_WIDTH = HM_WORD_WIDTH; // Width of the word in bits
  localparam DATA_WIDTH = HM_DATA_WIDTH; // 16 bits (only 14 bits used)
  localparam DATA_WIDTH_MUL = HM_DATA_WIDTH_MUL; // Data width for multiplication, larger than DATA_WIDTH
  localparam DATA_WIDTH_ACC = HM_DATA_WIDTH_ACC; // Data width for accumulator, larger than DATA_WIDTH
  localparam HSI_BANDS = HM_HSI_BANDS; // Number of HSI bands
  localparam HSI_LIBRARY_SIZE = HM_HSI_LIBRARY_SIZE; // Size of the HSI library
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);
  localparam DATA_PER_WORD = WORD_WIDTH / DATA_WIDTH; // Number of data elements per word
  localparam ELEMENTS = HSI_BANDS / DATA_PER_WORD; // Number of elements in the vector

  rand logic signed [DATA_WIDTH-1:0] measure [HSI_BANDS];

  // Generate random vectors
  constraint c_vctrs {
    // foreach (measure[i]) measure[i] inside {[0:(1 << DATA_WIDTH-2)-1]}; // Use values of 14 bits or less
    foreach (measure[i]) measure[i] inside {[0:9]}; // Use values of 14 bits or less
  }

  function automatic void fusion_vctr(
      input logic signed [DATA_WIDTH-1:0] vctr [HSI_BANDS],
      output logic [WORD_WIDTH-1:0] fusion_vctr [ELEMENTS]
    );
    for (int i = 0; i < HSI_BANDS; i+=2) begin
      fusion_vctr[i/2] = {vctr[i], vctr[i+1]};
    end
  endfunction

  function automatic void mse(
      input logic signed [DATA_WIDTH-1:0] vctr1 [HSI_BANDS],
      input logic signed [DATA_WIDTH-1:0] vctr2 [HSI_BANDS],
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
    mse = acc_aux  >> $clog2(HSI_BANDS); // Compute mean square error
  endfunction

  function automatic void acc_all(
      input logic signed [DATA_WIDTH-1:0] vctr1 [HSI_BANDS],
      input logic signed [DATA_WIDTH-1:0] vctr2 [HSI_BANDS],
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

  function automatic void min_max_mse(
      logic [WORD_WIDTH-1:0] expected_mse [HSI_LIBRARY_SIZE],
      output logic [WORD_WIDTH-1:0] min_mse_value,
      output logic [WORD_WIDTH-1:0] max_mse_value,
      output logic [HSI_LIBRARY_SIZE_ADDR-1:0] min_mse_ref,
      output logic [HSI_LIBRARY_SIZE_ADDR-1:0] max_mse_ref
    );
    logic [WORD_WIDTH-1:0] aux_min_mse_value = (1 << WORD_WIDTH) - 1; // Initialize to max value
    logic [WORD_WIDTH-1:0] aux_max_mse_value = '0; // Initialize to min value
    for (int i = 0; i < HSI_LIBRARY_SIZE; i++) begin
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