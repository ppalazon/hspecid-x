`timescale 1ns / 1ps

import hsid_pkg::*;

/*
 @WAVEDROM_START
 { "signal": [
 { "name": "clk",            "wave": "p..............................." },
 { "name": "rst_n",          "wave": "h..............................." },
 { "name": "clear",          "wave": "l..............................." },
 { "name": "band_pack_start","wave": "lhl........hl..................." },
 { "name": "band_pack_last", "wave": "l.........hl........hl.........." },
 { "name": "hsp_ref",        "wave": "x.........4x........4x..........", "data": ["3", "4"] },
 { "name": "band_pack_a",    "wave": "x33333333333333333333x..........", "data": ["0/1","2/3","4/5","6/7","8/9","9/8","7/6","5/4","3/2","1/0","0/1","2/3","4/5","6/7","8/9","9/8","7/6","5/4","3/2","1/0"] },
 { "name": "band_pack_b",    "wave": "x77777777779999999999x..........", "data": ["7/2","2/6","1/7","5/7","3/9","6/1","6/8","2/5","4/2","3/0","8/3","3/1","6/8","1/7","6/0","5/2","8/6","2/1","8/4","2/5"] },
 { "name": "band_pack_valid","wave": "lh...................l.........." },
 { "name": "hsp_bands",      "wave": "x.........2x........2x..........", "data": ["20","20"] },
 { "name": "mse_value",      "wave": "x...................5x........5x", "data": ["8","16"] },
 { "name": "mse_ref",        "wave": "x...................4x........4x", "data": ["3","4"] },
 { "name": "mse_valid",      "wave": "l...................hl........hl" },
 { "name": "acc_of",         "wave": "l..............................." }
 ]}
 @WAVEDROM_END
 */
module hsid_mse #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than WORD
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,
    input logic clear,
    input logic band_pack_start,
    input logic band_pack_last,
    input logic [HSP_LIBRARY_WIDTH-1:0] hsp_ref,
    input logic [WORD_WIDTH-1:0] band_pack_a, // Input sample word data
    input logic [WORD_WIDTH-1:0] band_pack_b, // Input sample word data
    input logic band_pack_valid,  // Enable input sample data
    input logic [HSP_BANDS_WIDTH-1:0] hsp_bands,  // HSP bands to process

    output logic [WORD_WIDTH-1:0] mse_value,  // Output mean square error
    output logic [HSP_LIBRARY_WIDTH-1:0] mse_ref,  // Reference vector for sum
    output logic mse_valid,  // Enable input sample data
    output logic acc_of
    // output logic mse_of
  );

  localparam HALF_WORD_WIDTH = WORD_WIDTH / 2; // Half of the word width
  localparam K = WORD_WIDTH;
  localparam DK = 2*K;
  localparam DIVIDEND_ZERO_FILL = {(DK - DATA_WIDTH_ACC){1'b0}}; // Suffix width for dividend
  localparam DIVISOR_ZERO_FILL = {(K - HSP_BANDS_WIDTH){1'b0}}; // Prefix width for divisor

  // Square difference accumulator outputs
  logic channel_1_acc_valid, channel_2_acc_valid;
  logic [DATA_WIDTH_ACC-1:0] channel_1_acc_value, channel_2_acc_value;
  logic channel_1_acc_last, channel_2_acc_last;
  logic channel_1_acc_of, channel_2_acc_of;  // Overflow flag for the accumulated vector

  // Catch the square difference accumulator outputs
  logic compute_acc_sum_en;  // Enable signal for mean square error accumulator

  assign compute_acc_sum_en = channel_1_acc_valid && channel_2_acc_valid
    && (channel_1_acc_last == channel_2_acc_last)
    && (channel_1_acc_last);

  // Pipeline stages for mean square error
  logic compute_mse_en;
  logic [DATA_WIDTH_ACC:0] acc_value;  // Accumulator for both channels
  logic [HSP_LIBRARY_WIDTH-1:0] acc_ref;  // Reference vector for mean square error
  logic [HSP_BANDS_WIDTH-1:0] acc_hsp_bands; // HSP bands to process
  logic acc_channel_of;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reset_values();
    end else begin
      if (clear) begin
        reset_values();
      end else begin
        // Pipeline stage for square difference accumulator between two channels
        if (band_pack_valid && band_pack_last) begin: last_band_pack
          acc_ref <= hsp_ref; // Set vector reference for sum
          acc_hsp_bands <= hsp_bands; // Set HSP bands to process
        end
        if (compute_acc_sum_en) begin: compute_acc_sum
          compute_mse_en <= 1;  // Enable mean square error accumulator
          acc_channel_of <= channel_1_acc_of || channel_2_acc_of;  // Check if any channel has overflow
          acc_value <= channel_1_acc_value + channel_2_acc_value;  // Sum the square differences
        end else begin
          compute_mse_en <= 0;  // Disable mean square error accumulator
        end

        // Pipeline stage for mean square error division
        // if (compute_mse_en) begin: compute_mse
        //   // Compute mean square error
        //   mse_valid <=1;  // Enable output
        //   // mse_of <= acc_value > (acc_hsp_bands * {WORD_WIDTH{1'b1}}); // Dividend is larger than the divisor * Max value of result
        //   mse_value <= acc_value / acc_hsp_bands;  // Divide by the number of bands
        //   acc_of <= acc_value[DATA_WIDTH_ACC] || acc_channel_of;  // Propagate overflow flag from square difference accumulator
        //   mse_ref <= acc_ref;  // Set reference vector for mean square error
        // end else begin
        //   mse_valid <= 0;  // Disable output when not valid
        // end
      end
    end
  end

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) channel_1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(band_pack_valid),  // Enable input sample data
    .initial_acc_en(band_pack_valid && band_pack_start),  // Enable initial accumulator value on first element
    .initial_acc('0),
    .data_in_a(band_pack_a[HALF_WORD_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_b(band_pack_b[HALF_WORD_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_last(band_pack_last),
    .acc_valid(channel_1_acc_valid),
    .acc_value(channel_1_acc_value),
    .acc_last(channel_1_acc_last),
    .clear(clear),  // Clean signal to reset the accumulator
    .acc_of(channel_1_acc_of)  // Overflow flag for the accumulated vector
  );

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) channel_2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(band_pack_valid),  // Enable input sample data
    .initial_acc_en(band_pack_valid && band_pack_start),
    .initial_acc('0),
    .data_in_a(band_pack_a[WORD_WIDTH-1:HALF_WORD_WIDTH]),  // Use the upper bits of the word
    .data_in_b(band_pack_b[WORD_WIDTH-1:HALF_WORD_WIDTH]),  //Use the upper bits of the word
    .data_in_last(band_pack_last),
    .acc_valid(channel_2_acc_valid),
    .acc_value(channel_2_acc_value),
    .acc_last(channel_2_acc_last),
    .clear(clear),  // Clean signal to reset the accumulator
    .acc_of(channel_2_acc_of)  // Overflow flag for the accumulated vector
  );

  hsid_divider #(
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .K(WORD_WIDTH)
  ) divider (
    .clk(clk),
    .rst_n(rst_n),
    .dividend({DIVIDEND_ZERO_FILL, acc_value}),  // Use only the lower bits of the accumulator
    .divisor({DIVISOR_ZERO_FILL, acc_hsp_bands}),
    .quotient(mse_value),
    .remainder(),
    .of_in(acc_value[DATA_WIDTH_ACC] || acc_channel_of), // Check if dividend is overflowed
    .hsp_ref_in(acc_ref),
    .overflow(acc_of),
    .start(compute_mse_en),
    .clear(clear),
    .ready(),
    .done(mse_valid),
    .hsp_ref_out(mse_ref),
    .idle()
  );

  task reset_values();
    begin
      // mse_ref <= 0;  // Reset reference vector
      // mse_value <= 0;  // Reset mean square error
      // mse_valid <= 0;  // Disable output
      // mse_of <= 0;  // Reset overflow flag for mean square error
      acc_channel_of <= 0;  // Reset overflow flag for the accumulated vector
      acc_hsp_bands <= 0; // Reset HSP bands to process
      compute_mse_en <= 0;  // Disable mean square error accumulator
      acc_value <= 0;  // Reset mean square error accumulator
      acc_ref <= 0;  // Reset reference vector for mean square error
      // acc_of <= 0;  // Reset overflow flag for mean square error accumulator
    end
  endtask

endmodule