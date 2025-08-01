
import hsid_pkg::*;

class HsidMseCompRandom #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Number of bits for HSI library size
  );

  localparam int MAX_WORD = {WORD_WIDTH{1'b1}}; // Maximum value for data vectors
  localparam int MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}}; // Maximum value for HSI library

  rand logic mse_in_valid;
  rand logic mse_in_of;
  rand logic [WORD_WIDTH-1:0] mse_in_value;
  rand logic [HSP_LIBRARY_WIDTH-1:0] mse_in_ref;
  rand logic clear;

  constraint clear_c {
    clear dist {0:=80, 1:=20}; // 80% chance to not clear, 20% chance to clear
  }

  constraint mse_in_valid_c {
    mse_in_valid dist {0:=30, 1:=70}; // 70% chance to have valid MSE input, 30% chance to not have valid input
  }

  constraint mse_in_of_c {
    mse_in_of dist {0:=90, 1:=10}; // 90% chance to not have overflow, 10% chance to have overflow
  }

  constraint mse_in_value_c {
    mse_in_value dist {0:=15, MAX_WORD:=15, [1:MAX_WORD-1]:/70}; // Distribute MSE values
  }

  constraint mse_in_ref_c {
    mse_in_ref dist {0:=15, MAX_HSP_LIBRARY:=15, [1:MAX_HSP_LIBRARY-1]:/70}; // Distribute MSE reference values
  }

endclass