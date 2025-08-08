`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidXTopGen #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int DATA_WIDTH = HSID_DATA_WIDTH, // 16 bits (only 14 bits used)
    parameter int DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter int DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Address width for HSP bands
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library
  ) extends HsidMainGen #(WORD_WIDTH, DATA_WIDTH, DATA_WIDTH_MUL, DATA_WIDTH_ACC, HSP_BANDS_WIDTH, HSP_LIBRARY_WIDTH);

  rand logic [WORD_WIDTH-1:0] captured_pixel_addr_w;
  rand logic [WORD_WIDTH-1:0] library_pixel_addr_w;
  rand logic get_close_hsp; // It's true, if the captured pixel would be in the library

  function void post_randomize();
    super.post_randomize();
    if (get_close_hsp) begin
      // Trying to reach similar hsp, where 4 pixels are the same as captured pixel data
      library_pixel_addr_w = captured_pixel_addr_w - (3 * hsp_bands_packs * 4);
    end
  endfunction

  constraint c_addr_word_alignment {
    captured_pixel_addr_w[1:0] == 2'b0;
    library_pixel_addr_w[1:0] == 2'b0;
  }

  constraint c_hsp_bands_even {
    // Ensure HSP bands are even for packing, and to avoid problems with memory because
    // it's difficult to generate lsb 0 bits on last pixel
    hsp_bands % 2 == 0;
  }

endclass