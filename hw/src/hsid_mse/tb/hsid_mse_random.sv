`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidHSPixelMseGen#(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits (only 14 bits used)
    parameter int DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter int DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Address width for HSP bands
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library
  ) extends HsidHSPixelGen #(DATA_WIDTH, DATA_WIDTH_MUL, DATA_WIDTH_ACC, HSP_BANDS_WIDTH, HSP_LIBRARY_WIDTH);

  logic [HSP_BANDS_WIDTH-1:0] hsp_bands_packs;
  rand logic [HSP_LIBRARY_WIDTH-1:0] vctr_ref; // Reference vector

  function void pre_randomize();
    super.pre_randomize();
    initial_acc.rand_mode(0); // This operand doesn't seem to work with xsim, so I repeat it after post_randomize
    initial_acc = 0; // Set initial accumulator value to zero
  endfunction

  function void post_randomize();
    super.post_randomize();
    hsp_bands_packs = (hsp_bands + 1) / 2;
    initial_acc = 0;
  endfunction

  constraint c_vctr_ref {
    vctr_ref dist {0:=15, MAX_HSP_LIBRARY:=15,  [1:MAX_HSP_LIBRARY-1]:/70};
  }

  // Ensure HSP bands are at least 8, to avoid problems with the latest steps of mse (3 of sq_df_acc + 1 of first mse pipeline)
  // I need 8 pixel because it will be packed in 2 pixels per word, so I need 6 (3x2 sq_df_acc) + 1 (mse of first mse pipelin) = 7
  constraint c_hsp_bands_bigger_than_six {
    hsp_bands >= 7;
    hsp_bands dist {7:=15, MAX_HSP_BANDS:=15, [6:MAX_HSP_BANDS-1]:/70};
  }

  function automatic void band_packer(
      input logic [DATA_WIDTH-1:0] hsp [], // HSP bands to process
      output logic [WORD_WIDTH-1:0] hsp_packed []
    );
    logic [DATA_WIDTH-1:0] i_plus_1;
    int packs = (hsp_bands + 1) / 2;
    int idx;
    hsp_packed = new[packs];
    for (int i = 0; i < packs; i+=1) begin
      idx = i*2;
      hsp_packed[i] = {hsp[idx], (idx+1==hsp_bands) ? {DATA_WIDTH{1'b0}} : hsp[idx+1]};
    end
  endfunction

  function automatic void mse(
      input logic [DATA_WIDTH_ACC:0] acc [], // Intermediate accumulator with overflow
      output logic [WORD_WIDTH-1:0] mse,
      output logic acc_of
      // output logic mse_of
    );
    logic [DATA_WIDTH_ACC:0] last_acc_sum = 0; // Accumulator for the sum
    acc_of = 0;
    // Check if the accumulator has overflown in any step
    for (int i = 0; i < hsp_bands; i++) begin
      if (acc[i][DATA_WIDTH_ACC]) begin
        acc_of = 1; // Set overflow flag if any accumulator has overflown
      end
    end
    last_acc_sum = acc[hsp_bands - 1];
    // mse_of = last_acc_sum > (hsp_bands * {WORD_WIDTH{1'b1}}); // Dividend is larger than the divisor * Max value of the divisor
    mse = last_acc_sum / hsp_bands; // Compute mean square error
  endfunction

  task display_hsp_packed(input string description, input logic [WORD_WIDTH-1:0] hsp []);
    int size = hsp.size();
    int limit = (size > 10) ? 10 : size;
    $write("%s: {", description);
    for (int i = 0; i < limit; i++) begin
      $write("0x%0h, ", hsp[i]);
    end
    if (size > limit) begin
      $write(" ... } (%0d more elements)", size - limit);
    end else begin
      $write("}");
    end
    $display("");
  endtask

endclass

class HsidMSERandom #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Address width for HSP bands
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library
  );

  rand logic clear;
  rand logic band_pack_start;
  rand logic band_pack_last;
  rand logic [HSP_LIBRARY_WIDTH-1:0] vctr_ref;
  rand logic [WORD_WIDTH-1:0] band_pack_a;
  rand logic [WORD_WIDTH-1:0] band_pack_b;
  rand logic band_pack_valid;
  rand logic [HSP_BANDS_WIDTH-1:0] hsp_bands;

  constraint c_hsp_bands_bigger_than_six {
    hsp_bands >= 5;
  }

endclass