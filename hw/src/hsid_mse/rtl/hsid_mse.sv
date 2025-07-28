`timescale 1ns / 1ps

import hsid_pkg::*;

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
    input logic [HSP_LIBRARY_WIDTH-1:0] vctr_ref,
    input logic [WORD_WIDTH-1:0] band_pack_a, // Input sample word data
    input logic [WORD_WIDTH-1:0] band_pack_b, // Input sample word data
    input logic band_pack_valid,  // Enable input sample data
    input logic [HSP_BANDS_WIDTH-1:0] hsi_bands,  // HSP bands to process

    output logic [WORD_WIDTH-1:0] mse_value,  // Output mean square error
    output logic [HSP_LIBRARY_WIDTH-1:0] mse_ref,  // Reference vector for sum
    output logic mse_valid,  // Enable input sample data
    output logic mse_of
  );

  // Number of data elements per word

  // Square difference accumulator outputs
  logic channel_1_acc_valid, channel_2_acc_valid;
  logic [DATA_WIDTH_ACC-1:0] channel_1_acc_value, channel_2_acc_value;
  logic channel_1_acc_last, channel_2_acc_last;
  logic [HSP_LIBRARY_WIDTH-1:0] channel_1_acc_ref, channel_2_acc_ref;  // Reference vector for sum
  logic channel_1_acc_of, channel_2_acc_of;  // Overflow flag for the accumulated vector

  // Catch the square difference accumulator outputs
  logic acc_sum_en;  // Enable signal for mean square error accumulator

  assign acc_sum_en = channel_1_acc_valid && channel_2_acc_valid &&
    channel_1_acc_of && channel_2_acc_of // Check if both channels have overflow
    && (channel_1_acc_ref == channel_2_acc_ref) // Check if both channels have the same reference vector
    && (channel_1_acc_last == channel_2_acc_last)
    && (channel_1_acc_last);

  // Pipeline statage for mean square error
  logic acc_valid;
  logic [DATA_WIDTH_ACC-1:0] acc_value;  // Accumulator for both channels
  logic [HSP_LIBRARY_WIDTH-1:0] acc_ref;  // Reference vector for mean square error
  logic acc_of;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reset();
    end if (clear) begin
      reset();
    end else begin
      // Pipeline stage for square difference accumulator between two channels
      if (acc_sum_en) begin
        acc_valid <= 1;  // Enable mean square error accumulator
        acc_ref <= channel_1_acc_ref;  // Set vector reference for sum
        {acc_of, acc_value} <= channel_1_acc_value + channel_2_acc_value;  // Sum the square differences
      end else begin
        acc_valid <= 0;  // Disable mean square error accumulator
      end

      // Pipeline stage for mean square error division
      if (acc_valid) begin
        // Compute mean square error
        mse_value <= acc_value / hsi_bands;  // Divide by the number of bands
        mse_ref <= acc_ref;  // Set reference vector for mean square error
        mse_valid <= !(acc_of);  // Enable output
        mse_of <= acc_of;  // Set overflow flag for mean square error
      end else begin
        mse_valid <= 0;  // Disable output when not valid
      end
    end
  end

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) channel_1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(band_pack_valid),  // Enable input sample data
    .initial_acc_en(band_pack_valid && band_pack_start),  // Enable initial accumulator value on first element
    .initial_acc('0),
    .data_in_a(band_pack_a[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_b(band_pack_b[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_ref(vctr_ref),
    .data_in_last(band_pack_last),
    .acc_valid(channel_1_acc_valid),
    .acc_value(channel_1_acc_value),
    .acc_last(channel_1_acc_last),
    .acc_ref(channel_1_acc_ref),
    .clear(clear),  // Clean signal to reset the accumulator
    .acc_of(channel_1_acc_of)  // Overflow flag for the accumulated vector
  );

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) channel_2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(band_pack_valid),  // Enable input sample data
    .initial_acc_en(band_pack_valid && band_pack_start),
    .initial_acc('0),
    .data_in_a(band_pack_a[WORD_WIDTH-1:DATA_WIDTH]),  // Use the upper bits of the word
    .data_in_b(band_pack_b[WORD_WIDTH-1:DATA_WIDTH]),  //Use the upper bits of the word
    .data_in_last(band_pack_last),
    .data_in_ref(vctr_ref),
    .acc_valid(channel_2_acc_valid),
    .acc_value(channel_2_acc_value),
    .acc_last(channel_2_acc_last),
    .acc_ref(channel_2_acc_ref),
    .clear(clear),  // Clean signal to reset the accumulator
    .acc_of(channel_2_acc_of)  // Overflow flag for the accumulated vector
  );

  task reset();
    begin
      mse_ref <= 0;  // Reset reference vector
      mse_value <= 0;  // Reset mean square error
      mse_valid <= 0;  // Disable output
      mse_of <= 0;  // Reset overflow flag for mean square error
      acc_valid <= 0;  // Disable mean square error accumulator
      acc_value <= 0;  // Reset mean square error accumulator
      acc_ref <= 0;  // Reset reference vector for mean square error
      acc_of <= 0;  // Reset overflow flag for mean square error accumulator
    end
  endtask

endmodule