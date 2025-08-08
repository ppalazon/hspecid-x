`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidXCtrlRegRandom #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH
  );

  localparam int MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}};
  localparam int MAX_HSP_BANDS = {HSP_BANDS_WIDTH{1'b1}};
  localparam int MAX_WORD = {WORD_WIDTH{1'b1}};

  rand logic [HSP_BANDS_WIDTH-1:0] hsp_bands; // Number of HSP bands
  rand logic [HSP_LIBRARY_WIDTH-1:0] hsp_library_size; // Size of the HSP library
  rand logic [WORD_WIDTH-1:0] captured_pixel_addr; // Address of the captured pixel
  rand logic [WORD_WIDTH-1:0] library_pixel_addr; // Address of the library pixel
  rand logic start;
  rand logic clear;
  rand logic ready;
  rand logic idle;
  rand logic done;
  rand logic error;
  rand logic interrupt;

  rand logic [HSP_LIBRARY_WIDTH-1:0] mse_min_ref;
  rand logic [WORD_WIDTH-1:0] mse_min_value;
  rand logic [HSP_LIBRARY_WIDTH-1:0] mse_max_ref;
  rand logic [WORD_WIDTH-1:0] mse_max_value;

  constraint c_hsp_bands {
    hsp_bands dist {0:=15, MAX_HSP_BANDS:=15, [1:MAX_HSP_BANDS-1]:/70};
  }

  constraint c_hsp_library_size {
    hsp_library_size dist {0:=15, MAX_HSP_LIBRARY:=15, [1:MAX_HSP_LIBRARY-1]:/70};
  }

  constraint c_captured_pixel_addr {
    captured_pixel_addr dist {0:=15, MAX_WORD:=15, [1:MAX_WORD-1]:/70};
  }

  constraint c_library_pixel_addr {
    library_pixel_addr dist {0:=15, MAX_WORD:=15, [1:MAX_WORD-1]:/70};
  }

  constraint c_mse_min_ref {
    mse_min_ref dist {0:=15, MAX_HSP_LIBRARY:=15, [1:MAX_HSP_LIBRARY-1]:/70};
  }

  constraint c_mse_max_ref {
    mse_max_ref dist {0:=15, MAX_HSP_LIBRARY:=15, [1:MAX_HSP_LIBRARY-1]:/70};
  }

  constraint c_mse_min_value {
    mse_min_value dist {0:=15, MAX_WORD:=15, [1:MAX_WORD-1]:/70};
  }

  constraint c_mse_max_value {
    mse_max_value dist {0:=15, MAX_WORD:=15, [1:MAX_WORD-1]:/70};
  }

endclass