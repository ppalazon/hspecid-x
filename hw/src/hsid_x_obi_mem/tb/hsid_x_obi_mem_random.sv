`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidXObiMemRandom#(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter int MEM_ACCESS_WIDTH = HSID_MEM_ACCESS_WIDTH // Address width for HSP bands
  );

  rand logic [WORD_WIDTH-1:0] initial_addr;
  rand logic [MEM_ACCESS_WIDTH-1:0] requests;

endclass