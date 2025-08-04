`timescale 1ns / 1ps

import hsid_pkg::*;

class hsid_fifo_op #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the data in bits
    parameter FIFO_ADDR_WIDTH = HSID_FIFO_ADDR_WIDTH // Address width for FIFO depth
  );

  localparam FIFO_DEPTH = 2 ** FIFO_ADDR_WIDTH; // Define FIFO depth based on address width

  rand logic [WORD_WIDTH-1:0] data_in;
  rand logic wr_en;
  rand logic rd_en;
  rand logic clear;
  rand logic loop_en;
  rand logic [FIFO_ADDR_WIDTH-1:0] almost_full_threshold;

  rand int repeat_op; // Random number of operations to perform

  constraint clear_c {
    clear dist {0:=80, 1:=20}; // 80% chance to not clear, 20% chance to clear
  }

  constraint loop_en_c {
    loop_en dist {0:=70, 1:=30}; // 70% chance to not loop, 30% chance to loop
  }

  constraint repeat_op_c {
    clear == 1 -> repeat_op == 1; // If clear is set, repeat_op should be 1
    clear == 0 -> repeat_op inside {[1:FIFO_DEPTH+1]}; // If clear is not set, repeat_op can be between 1 and FIFO_DEPTH+1
  }

endclass