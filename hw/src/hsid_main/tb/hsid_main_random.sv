`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidMainGen #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits (only 14 bits used)
    parameter int DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter int DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Address width for HSP bands
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library
  ) extends HsidHSPixelMseGen #(WORD_WIDTH, DATA_WIDTH, DATA_WIDTH_MUL, DATA_WIDTH_ACC, HSP_BANDS_WIDTH, HSP_LIBRARY_WIDTH);

  rand logic test_rnd_insert; // Enable random insertion of test vectors
  rand logic [HSP_LIBRARY_WIDTH-1:0] library_size;

  constraint c_library_size {
    library_size dist {1:=15, MAX_HSP_LIBRARY:=15, [1:MAX_HSP_LIBRARY-1]:/70};
    // library_size inside {[1:10]};
  }

  function automatic void min_max_mse(
      logic [WORD_WIDTH-1:0] expected_mse [],
      output logic [WORD_WIDTH-1:0] min_mse_value,
      output logic [WORD_WIDTH-1:0] max_mse_value,
      output logic [HSP_LIBRARY_WIDTH-1:0] min_mse_ref,
      output logic [HSP_LIBRARY_WIDTH-1:0] max_mse_ref
    );
    logic [WORD_WIDTH-1:0] aux_min_mse_value = {WORD_WIDTH{1'b1}};
    logic [WORD_WIDTH-1:0] aux_max_mse_value = '0; // Initialize to min value
    for (int i = 0; i < library_size; i++) begin
      if (expected_mse[i] <= aux_min_mse_value) begin
        aux_min_mse_value = expected_mse[i];
        min_mse_ref = i;
      end
      if (expected_mse[i] >= aux_max_mse_value) begin
        aux_max_mse_value = expected_mse[i];
        max_mse_ref = i;
      end
    end
    min_mse_value = aux_min_mse_value;
    max_mse_value = aux_max_mse_value;
  endfunction
endclass

class HsidHSPReferenceGen#(
    parameter int DATA_WIDTH = HSID_DATA_WIDTH,
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH
  );

  localparam int MAX_DATA = {DATA_WIDTH{1'b1}}; // Maximum value for data vectors

  logic [HSP_BANDS_WIDTH-1:0] hsp_bands; // Number of HSP bands
  rand logic [DATA_WIDTH-1:0] reference_hsp [];

  constraint c_reference_hsp {
    reference_hsp.size == hsp_bands;
    foreach (reference_hsp[i]) reference_hsp[i] dist {0:=15, MAX_DATA:=15, [1:MAX_DATA-1]:/70};
    // foreach (reference_hsp[i]) reference_hsp[i] inside {[0:10]};
  }
endclass

class HsidHSPSimpleGen#(
    parameter int DATA_WIDTH = HSID_DATA_WIDTH,
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH
  );

  localparam int MAX_DATA = 100; // Maximum value for data vectors

  logic [HSP_BANDS_WIDTH-1:0] hsp_bands; // Number of HSP bands
  rand logic [DATA_WIDTH-1:0] reference_hsp [];

  constraint c_reference_hsp {
    reference_hsp.size == hsp_bands;
    foreach (reference_hsp[i]) reference_hsp[i] dist {0:=15, MAX_DATA:=15, [1:MAX_DATA-1]:/70};
    // foreach (reference_hsp[i]) reference_hsp[i] inside {[0:10]};
  }
endclass

class HsidMainRandom #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Address width for HSP bands
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library
  );

  rand logic rst_n;
  rand logic clear;
  rand logic band_data_in_valid;
  rand logic [WORD_WIDTH-1:0] band_data_in;
  rand logic [HSP_LIBRARY_WIDTH-1:0] hsp_library_size_in;
  rand logic [HSP_BANDS_WIDTH-1:0] hsp_bands_in;
  rand logic start;

  constraint c_clear {
    clear dist {0:=90, 1:=10}; // 80% chance to not clear, 20% chance to clear
  }

  constraint c_rst_n {
    rst_n dist {0:=10, 1:=90}; // 10% chance to reset, 90% chance to not reset
  }

  constraint c_band_data_in_valid {
    band_data_in_valid dist {0:=10, 1:=90}; // 70% chance to have valid band data input, 30% chance to not have valid input
  }

  constraint c_band_data_in {
    band_data_in dist {0:=15, {WORD_WIDTH{1'b1}}:=15, [1:{WORD_WIDTH{1'b1}}-1]:/70}; // Distribute band data values
  }

  constraint c_hsp_library_size_in {
    hsp_library_size_in dist {0:=15, {HSP_LIBRARY_WIDTH{1'b1}}:=15, [1:{HSP_LIBRARY_WIDTH{1'b1}}-1]:/70}; // Distribute HSP library size values
  }

  constraint c_hsp_bands_in {
    hsp_bands_in dist {0:=15, {HSP_BANDS_WIDTH{1'b1}}:=15, [1:{HSP_BANDS_WIDTH{1'b1}}-1]:/70}; // Distribute HSP bands values
  }

  constraint c_start {
    start dist {1:=80, 0:=20}; // 80% chance to not start, 20% chance to start
  }

endclass