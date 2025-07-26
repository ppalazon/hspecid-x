`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidSqDfAccGen #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH
  );

  rand logic [HSP_BANDS_WIDTH-1:0] hsp_bands; // Number of HSI bands
  rand logic signed [DATA_WIDTH-1:0] vctr1 [];
  rand logic signed [DATA_WIDTH-1:0] vctr2 [];
  rand logic [DATA_WIDTH_ACC-1:0] initial_acc; // Initial accumulator value

  // Generate random vectors
  constraint c_hsp_bands {
    hsp_bands dist {1:=20, 2**HSP_BANDS_WIDTH:=20, [2:(2**HSP_BANDS_WIDTH) - 1]:/60};
  }

  constraint c_vctrs {
    vctr1.size == hsp_bands;
    vctr2.size == hsp_bands;
    foreach (vctr1[i]) vctr1[i] inside {[0:(1 << DATA_WIDTH-2)-1]}; // Use values of 14 bits or less
    foreach (vctr2[i]) vctr2[i] inside {[0:(1 << DATA_WIDTH-2)-1]};

    // foreach (vctr1[i]) vctr1[i] inside {[0:99]};
    // foreach (vctr2[i]) vctr2[i] inside {[0:99]};
    // initial_acc inside {[0:10]};
  }

  function automatic void sq_df_acc_vctr(
      output logic [DATA_WIDTH_ACC-1:0]   acc [] // wider to hold overflow
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC-1:0] acc_aux = initial_acc; // Accumulator for the output
    acc = new[hsp_bands];
    for (int i = 0; i < hsp_bands; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      acc[i] = acc_aux; // Store the accumulated value
    end
  endfunction

endclass