`timescale 1ns / 1ps

module hsid_mse #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = 32,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = 48,  // Data width for accumulator, larger than WORD
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)  // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    input logic element_start,
    input logic element_last,
    input logic [HSI_LIBRARY_SIZE_ADDR-1:0] vctr_ref,
    input logic [WORD_WIDTH-1:0] element_a, // Input sample word data
    input logic [WORD_WIDTH-1:0] element_b, // Input sample word data
    input logic element_valid,  // Enable input sample data

    output logic [WORD_WIDTH-1:0] mse_value,  // Output mean square error
    output logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_ref,  // Reference vector for sum
    output logic mse_valid  // Enable input sample data
  );

  // Number of data elements per word

  // Square difference accumulator outputs
  logic channel_1_acc_valid, channel_2_acc_valid;
  logic [DATA_WIDTH_ACC-1:0] channel_1_acc_value, channel_2_acc_value;
  logic channel_1_acc_last, channel_2_acc_last;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] channel_1_acc_ref, channel_2_acc_ref;  // Reference vector for sum

  // Catch the square difference accumulator outputs
  logic acc_sum_en;  // Enable signal for mean square error accumulator

  assign acc_sum_en = channel_1_acc_valid && channel_2_acc_valid
    && (channel_1_acc_ref == channel_2_acc_ref) // Check if both channels have the same reference vector
    && (channel_1_acc_last == channel_2_acc_last)
    && (channel_1_acc_last);


  // Pipeline statage for mean square error
  logic acc_valid;
  logic [DATA_WIDTH_ACC:0] acc_value;  // Accumulator for both channels
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] acc_ref;  // Reference vector for mean square error

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mse_ref <= 0;  // Reset reference vector
      mse_value <= 0;  // Reset mean square error
      mse_valid <= 0;  // Disable output
      acc_valid <= 0;  // Disable mean square error accumulator
      acc_value <= 0;  // Reset mean square error accumulator
      acc_ref <= 0;  // Reset reference vector for mean square error
    end else begin

      // Pipeline stage for square difference accumulator between two channels
      if (acc_sum_en) begin
        acc_valid <= 1;  // Enable mean square error accumulator
        acc_ref <= channel_1_acc_ref;  // Set vector reference for sum
        acc_value <= channel_1_acc_value + channel_2_acc_value;  // Sum the square differences
      end else begin
        acc_valid <= 0;  // Disable mean square error accumulator
      end

      // Pipeline stage for mean square error division
      if (acc_valid) begin
        // Compute mean square error
        mse_value <= acc_value >> HSI_BANDS_ADDR;  // Divide by the number of bands
        mse_ref <= acc_ref;  // Set reference vector for mean square error
        mse_valid <= 1;  // Enable output
      end else begin
        mse_valid <= 0;  // Disable output when not valid
      end
    end
  end

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) channel_1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(element_valid),  // Enable input sample data
    .initial_acc_en(element_valid && element_start),  // Enable initial accumulator value on first element
    .initial_acc('0),
    .data_in_a(element_a[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_b(element_b[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_ref(vctr_ref),
    .data_in_last(element_last),
    .acc_valid(channel_1_acc_valid),
    .acc_value(channel_1_acc_value),
    .acc_last(channel_1_acc_last),
    .acc_ref(channel_1_acc_ref)
  );

  hsid_sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) channel_2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(element_valid),  // Enable input sample data
    .initial_acc_en(element_valid && element_start),
    .initial_acc('0),
    .data_in_a(element_a[WORD_WIDTH-1:DATA_WIDTH]),  // Use the upper bits of the word
    .data_in_b(element_b[WORD_WIDTH-1:DATA_WIDTH]),  //Use the upper bits of the word
    .data_in_last(element_last),
    .data_in_ref(vctr_ref),
    .acc_valid(channel_2_acc_valid),
    .acc_value(channel_2_acc_value),
    .acc_last(channel_2_acc_last),
    .acc_ref(channel_2_acc_ref)
  );

endmodule