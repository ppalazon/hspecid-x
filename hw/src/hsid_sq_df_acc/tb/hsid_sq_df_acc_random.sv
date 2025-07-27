`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidSqDfAccGen #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH
  );

  localparam int MAX_DATA = (1 << DATA_WIDTH) - 1; // Maximum value for data vectors
  localparam logic[DATA_WIDTH_ACC-1:0] MAX_DATA_ACC = (1 << DATA_WIDTH_ACC) - 1; // Maximum value for accumulator, it's wider than 32 bits
  localparam int MAX_HSP_BANDS = (1 << HSP_BANDS_WIDTH) - 1; // Maximum value for HSI bands
  localparam int MAX_HSP_LIBRARY = (1 << HSP_LIBRARY_WIDTH) - 1; // Maximum value for HSI library

  rand logic [HSP_LIBRARY_WIDTH-1:0] vctr_ref; // Reference vector, avoid repetition
  rand logic [HSP_BANDS_WIDTH-1:0] hsp_bands; // Number of HSI bands
  rand logic [DATA_WIDTH-1:0] vctr1 [];
  rand logic [DATA_WIDTH-1:0] vctr2 [];
  rand logic [DATA_WIDTH_ACC-1:0] initial_acc; // Initial accumulator value

  // Generate random vectors
  constraint c_hsp_bands {
    hsp_bands dist {1:=15, MAX_HSP_BANDS:=15, [2:MAX_HSP_BANDS-1]:/70};
  }

  constraint c_vctrs {
    vctr1.size == hsp_bands;
    vctr2.size == hsp_bands;
    foreach (vctr1[i]) vctr1[i] dist {0:=15, MAX_DATA:=15, [1:MAX_DATA-1]:/70};
    foreach (vctr2[i]) vctr2[i] dist {0:=15, MAX_DATA:=15, [1:MAX_DATA-1]:/70};

    // foreach (vctr1[i]) vctr1[i] inside {[0:10]};
    // foreach (vctr2[i]) vctr2[i] inside {[0:10]};
    // initial_acc inside {[0:10]};
  }

  constraint c_vctr_ref {
    vctr_ref dist {0:=15, MAX_HSP_LIBRARY:=15,  [1:MAX_HSP_LIBRARY-1]:/70};
  }

  constraint c_initial_acc {
    initial_acc dist {0:=15, MAX_DATA_ACC:=15, [1:MAX_DATA_ACC-1]:/70};
  }

  function void sq_df_acc_vctr(
      output logic [DATA_WIDTH_ACC-1:0]   acc[], // wider to hold overflow
      output logic overflow // overflow flag
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC:0] acc_aux = initial_acc; // Accumulator for the output
    acc = new[hsp_bands];
    for (int i = 0; i < hsp_bands; i++) begin
      diff = vctr1[i] - vctr2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      acc[i] = acc_aux; // Store the accumulated value
    end
    overflow = acc_aux[DATA_WIDTH_ACC]; // Check for overflow in the last bit
  endfunction

endclass