`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidHSPixelGen #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH
  );

  localparam int                       MAX_DATA = {DATA_WIDTH{1'b1}}; // Maximum value for data vectors
  localparam logic[DATA_WIDTH_ACC-1:0] MAX_DATA_ACC = {DATA_WIDTH_ACC{1'b1}}; // Maximum value for accumulator, it's wider than 32 bits
  localparam int                       MAX_HSP_BANDS = {HSP_BANDS_WIDTH{1'b1}}; // Maximum value for HSP bands
  localparam int                       MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}}; // Maximum value for HSI library

  rand logic [HSP_BANDS_WIDTH-1:0] hsp_bands; // Number of HSP bands
  rand logic [DATA_WIDTH-1:0] vctr1 [];
  rand logic [DATA_WIDTH-1:0] vctr2 [];
  rand logic [DATA_WIDTH_ACC-1:0] initial_acc; // Initial accumulator value

  // Generate random vectors
  constraint c_hsp_bands {
    hsp_bands dist {1:=15, MAX_HSP_BANDS:=15, [2:MAX_HSP_BANDS-1]:/70};
    // hsp_bands == 16;
  }

  constraint c_vctrs {
    vctr1.size == hsp_bands;
    vctr2.size == hsp_bands;
    foreach (vctr1[i]) vctr1[i] dist {0:=15, MAX_DATA:=15, [1:MAX_DATA-1]:/70};
    foreach (vctr2[i]) vctr2[i] dist {0:=15, MAX_DATA:=15, [1:MAX_DATA-1]:/70};

    // foreach (vctr1[i]) vctr1[i] inside {[0:10]};
    // foreach (vctr2[i]) vctr2[i] inside {[0:10]};
  }

  constraint c_initial_acc {
    initial_acc dist {0:=15, MAX_DATA_ACC:=15, [1:MAX_DATA_ACC-1]:/70};
    // initial_acc inside {[0:10]};
  }

  function void sq_df_acc_vctr(
      input logic [DATA_WIDTH-1:0] v1 [], // Input vector 1
      input logic [DATA_WIDTH-1:0] v2 [], // Input vector
      output logic [DATA_WIDTH_ACC:0]   acc[] // Intermediate accumulator with overflow
    );
    logic signed [DATA_WIDTH:0] diff; // Difference between elements
    logic [DATA_WIDTH_MUL-1:0] mult; // Multiplication result
    logic [DATA_WIDTH_ACC:0] acc_aux = initial_acc; // Accumulator for the output
    acc = new[hsp_bands];
    for (int i = 0; i < hsp_bands; i++) begin
      diff = v1[i] - v2[i]; // Compute difference
      mult = diff * diff; // Compute squared difference
      acc_aux += mult; // Accumulate the result
      acc[i] = acc_aux; // Store the accumulated value
    end
  endfunction

  function void set_worst_case_for_acc(
      input logic [HSP_BANDS_WIDTH-1:0] hsp_bands_i // Number of HSP bands
    );
    hsp_bands = hsp_bands_i; // Set maximum number of HSP bands
    vctr1 = new[hsp_bands];
    vctr2 = new[hsp_bands];
    foreach (vctr1[i]) vctr1[i] = MAX_DATA; // Set all elements to maximum value
    foreach (vctr2[i]) vctr2[i] = 0;
  endfunction

  task display_hsp(input string description, input logic [DATA_WIDTH-1:0] hsp []);
    int size = hsp.size();
    $write("%s: {", description);
    if (size > 10) begin
      int limit = 5;
      for (int i = 0; i < limit; i++) begin
        $write("0x%0h, ", hsp[i]);
      end
      $write(" ... ");
      for (int i = size - limit; i < size; i++) begin
        $write("0x%0h, ", hsp[i]);
      end
    end else begin
      for (int i = 0; i < size; i++) begin
        $write("0x%0h, ", hsp[i]);
      end
    end
    $write("}");
    $display("");
  endtask

endclass

class HsidSQDFAccRandom #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits by default
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC // Data width for accumulator, larger than DATA_WIDTH
  );

  rand logic clear;
  rand logic initial_acc_en; // Enable initial accumulator value
  rand logic [DATA_WIDTH_ACC-1:0] initial_acc; // Initial accumulator value
  rand logic data_in_valid; // Valid input values
  rand logic [DATA_WIDTH-1:0] data_in_a; // Input vector 1
  rand logic [DATA_WIDTH-1:0] data_in_b; // Input vector 2
  rand logic data_in_last;

endclass