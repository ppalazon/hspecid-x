`timescale 1ns / 1ps

module hsi_mse_reg #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = 32,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = 48,  // Data width for accumulator, larger than WORD
    parameter HSI_BANDS = 128,  // Number of HSI bands
    localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    parameter HSI_LIBRARY_SIZE = 256,  // Size of the HSI library
    localparam  HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)
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

  // logic [ELEMENTS_ADDR-1:0] band_counter;  // Band counter for HSI bands

  // Register for input samples
  logic [WORD_WIDTH-1:0] element_a_reg;  // Register for input sample a
  logic [WORD_WIDTH-1:0] element_b_reg;  // Register for input sample b
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] vctr_ref_reg;  // Register for reference vector

  // Initial accumulator
  logic initial_acc_en;  // Enable signal for initial accumulator value
  logic [DATA_WIDTH_ACC-1:0] initial_acc;  // Initial accumulator value

  // Square difference accumulator outputs
  logic channel_1_acc_valid, channel_2_acc_valid;
  logic [DATA_WIDTH_ACC-1:0] channel_1_acc_value, channel_2_acc_value;
  logic channel_1_acc_last, channel_2_acc_last;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] channel_1_acc_ref, channel_2_acc_ref;  // Reference vector for sum

  // Catch the square difference accumulator outputs
  logic sq_df_acc_en, sq_df_acc_last;
  // logic last_element_vctr;  // Enable signal for square difference accumulator
  logic acc_sum_en;  // Enable signal for mean square error accumulator

  assign acc_sum_en = channel_1_acc_valid && channel_2_acc_valid
    && (channel_1_acc_ref == channel_2_acc_ref) // Check if both channels have the same reference vector
    && (channel_1_acc_last == channel_2_acc_last)
    && (channel_1_acc_last);

  // assign last_element_vctr = (band_counter == ELEMENTS - 1);  // Check if last element of the vector

  // Pipeline statage for mean square error
  logic acc_valid;
  logic [DATA_WIDTH_ACC:0] acc_value;  // Accumulator for both channels
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] acc_ref;  // Reference vector for mean square error

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mse_ref <= 0;  // Reset reference vector
      mse_value <= 0;  // Reset mean square error
      mse_valid <= 0;  // Disable output
      // band_counter <= 0;  // Reset band counter
      sq_df_acc_last <= 0;  // Clear last element flag for square difference accumulator
      initial_acc_en <= 0;  // Disable initial accumulator value
      initial_acc <= 0;  // Reset initial accumulator value
      sq_df_acc_en <= 0;  // Disable square difference accumulator
      element_a_reg <= 0;  // Reset input sample a register
      element_b_reg <= 0;  // Reset input sample b register
      vctr_ref_reg <= 0;  // Reset reference vector register
      acc_valid <= 0;  // Disable mean square error accumulator
      acc_value <= 0;  // Reset mean square error accumulator
      acc_ref <= 0;  // Reset reference vector for mean square error
    end else begin
      // Set initial accumulator value on first element
      if (element_valid) begin
        element_a_reg <= element_a;  // Use only the lower bits of the word
        element_b_reg <= element_b;  // Use only
        vctr_ref_reg <= vctr_ref;  // Set reference vector for sum
        sq_df_acc_en <= 1;  // Enable square difference accumulator
        if (element_start) begin
          // band_counter <= 0;  // Reset band counter on start signal
          initial_acc_en <= 1;  // Enable initial accumulator value on first element
          initial_acc <= 0;  // Initial value it's always zero
        end else begin
          // band_counter <= band_counter + 1;  // Increment band counter
          initial_acc_en <= 0;  // Disable initial accumulator value after first element
        end
        if (element_last) begin
          sq_df_acc_last <= 1;  // Set last element flag for square difference accumulator
        end else begin
          sq_df_acc_last <= 0;  // Clear last element flag for square difference accumulator
        end
      end
      else begin
        sq_df_acc_en <= 0;  // Disable square difference accumulator when no valid input
      end

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

  sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) channel_1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(sq_df_acc_en),
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_a(element_a_reg[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_b(element_b_reg[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_ref(vctr_ref_reg),
    .data_in_last(sq_df_acc_last),
    .acc_valid(channel_1_acc_valid),
    .acc_value(channel_1_acc_value),
    .acc_last(channel_1_acc_last),
    .acc_ref(channel_1_acc_ref)
  );

  sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  ) channel_2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(sq_df_acc_en),
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_a(element_a_reg[WORD_WIDTH-1:DATA_WIDTH]),  // Use the upper bits of the word
    .data_in_b(element_b_reg[WORD_WIDTH-1:DATA_WIDTH]),  //Use the upper bits of the word
    .data_in_last(sq_df_acc_last),
    .data_in_ref(vctr_ref_reg),
    .acc_valid(channel_2_acc_valid),
    .acc_value(channel_2_acc_value),
    .acc_last(channel_2_acc_last),
    .acc_ref(channel_2_acc_ref)
  );



endmodule