`timescale 1ns / 1ps

import hsid_pkg::*;

class HsidDividerRnd  #(
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter K = 32,
    localparam DK = 2*K
  );

  localparam MAX_DIVIDEND = {DK{1'b1}};
  localparam MAX_DIVISOR = {K{1'b1}};
  localparam MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}};

  rand logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref_in;
  rand logic [DK-1:0] dividend;
  rand logic [K-1:0] divisor;
  rand logic clear;
  rand logic start;
  rand logic of_in;

  logic [K-1:0] expected_quotient;
  logic [K-1:0] expected_remainder;
  logic expected_overflow;

  constraint c_hsp_ref_in {
    hsp_ref_in dist {0:=15, MAX_HSP_LIBRARY:=15, [1:MAX_HSP_LIBRARY-1]:/70};
  }

  constraint c_clear {
    clear dist {0:=90, 1:=10}; // 80% chance to not clear, 20% chance to clear
  }

  constraint c_dividend {
    dividend dist {0:=15, MAX_DIVISOR:=15, MAX_DIVIDEND:=15, [1:MAX_DIVIDEND-1]:/55};
  }

  constraint c_divisor {
    divisor dist {0:=5, 1:=15, MAX_DIVISOR:=15, [2:MAX_DIVISOR-1]:/65}; // Avoid zero divisor
  }

  constraint c_of_in {
    of_in dist {0:=95, 1:=5}; // 80% chance to not overflow, 20% chance to overflow
  }

  function void post_randomize();
    if (divisor != 0) begin
      expected_quotient = dividend / divisor;
      expected_remainder = dividend % divisor;
    end
    expected_overflow = of_in || ((divisor == 0) || (dividend >= {{K{1'b0}}, divisor} << K));
  endfunction : post_randomize

endclass