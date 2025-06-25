`timescale 1ns / 1ps

module hsi_mse #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = 32,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = 48,  // Data width for accumulator, larger than WORD
    parameter DATA_PER_WORD = WORD_WIDTH / DATA_WIDTH,  // Number of data elements per word
    parameter HSI_BANDS = 128,  // Number of HSI bands
    parameter ELEMENTS = HSI_BANDS / DATA_PER_WORD,  // Number of elements in the vector
    parameter ELEMENTS_ADDR = $clog2(HSI_BANDS)  // Address width for HSI bands
  ) (
    input logic clk,
    input logic rst_n,

    input logic start_vctr,
    input logic [WORD_WIDTH-1:0] element_a, // Input sample word data
    input logic [WORD_WIDTH-1:0] element_b, // Input sample word data
    input logic element_valid,  // Enable input sample data

    output logic [WORD_WIDTH-1:0] mse,  // Output mean square error
    output logic mse_valid  // Enable input sample data
  );

  logic [ELEMENTS_ADDR-1:0] band_counter;  // Band counter for HSI bands

  // Enable signal for square difference accumulator
  logic sq_df_acc_en;

  // Register for input samples
  logic [WORD_WIDTH-1:0] element_a_reg;  // Register for input sample a
  logic [WORD_WIDTH-1:0] element_b_reg;  // Register for input sample b

  // Initial accumulator
  logic initial_acc_en;  // Enable signal for initial accumulator value
  logic [DATA_WIDTH_ACC-1:0] initial_acc;  // Initial accumulator value

  // Square difference accumulator outputs
  logic channel_1_acc_valid;
  logic channel_2_acc_valid;
  logic [DATA_WIDTH_ACC-1:0] channel_1_acc;
  logic [DATA_WIDTH_ACC-1:0] channel_2_acc;
  logic [ELEMENTS_ADDR-1:0] channel_1_element_out;
  logic [ELEMENTS_ADDR-1:0] channel_2_element_out;

  // Catch the square difference accumulator outputs
  logic sq_df_acc_finish;

  assign sq_df_acc_finish = channel_1_acc_valid && channel_2_acc_valid
    && (channel_1_element_out == channel_2_element_out)
    && (channel_1_element_out == ELEMENTS - 1);

  // Pipeline statage for mean square error
  logic mse_acc_valid;
  logic [DATA_WIDTH_ACC:0] mse_acc;  // Accumulator for both channels

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mse <= 0;  // Reset mean square error
      mse_valid <= 0;  // Disable output
      band_counter <= 0;  // Reset band counter
      initial_acc_en <= 0;  // Disable initial accumulator value
      initial_acc <= 0;  // Reset initial accumulator value
      sq_df_acc_en <= 0;  // Disable square difference accumulator
      element_a_reg <= 0;  // Reset input sample a register
      element_b_reg <= 0;  // Reset input sample b register
      mse_acc_valid <= 0;  // Disable mean square error accumulator
      mse_acc <= 0;  // Reset mean square error accumulator
    end else begin
      // Set initial accumulator value on first element
      if (element_valid) begin
        element_a_reg <= element_a;  // Use only the lower bits of the word
        element_b_reg <= element_b;  // Use only
        sq_df_acc_en <= 1;  // Enable square difference accumulator
        if (start_vctr) begin
          band_counter <= 0;  // Reset band counter on start signal
          initial_acc_en <= 1;  // Enable initial accumulator value on first element
          initial_acc <= 0;  // Initial value it's always zero
        end else begin
          band_counter <= band_counter + 1;  // Increment band counter
          initial_acc_en <= 0;  // Disable initial accumulator value after first element
        end
      end else begin
        sq_df_acc_en <= 0;  // Disable square difference accumulator when no valid input
      end

      // Pipeline stage for square difference accumulator between two channels
      if (sq_df_acc_finish) begin
        mse_acc_valid <= 1;  // Enable mean square error accumulator
        mse_acc <= channel_1_acc + channel_2_acc;  // Sum the square differences
      end else begin
        mse_acc_valid <= 0;  // Disable mean square error accumulator
      end

      // Pipeline stage for mean square error division
      if (mse_acc_valid) begin
        // Compute mean square error
        mse <= mse_acc >> ELEMENTS_ADDR;  // Divide by the number of bands
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
    .HSI_BANDS(HSI_BANDS)
  ) channel_1 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(sq_df_acc_en),
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_v1(element_a_reg[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .data_in_v2(element_b_reg[DATA_WIDTH-1:0]),  // Use only the lower bits of the word
    .acc_valid(channel_1_acc_valid),
    .acc_out(channel_1_acc),
    .element(band_counter),
    .element_out(channel_1_element_out)
  );

  sq_df_acc #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSI_BANDS(HSI_BANDS)
  ) channel_2 (
    .clk(clk),
    .rst_n(rst_n),
    .data_in_valid(sq_df_acc_en),
    .initial_acc_en(initial_acc_en),
    .initial_acc(initial_acc),
    .data_in_v1(element_a_reg[WORD_WIDTH-1:DATA_WIDTH]),  // Use the upper bits of the word
    .data_in_v2(element_b_reg[WORD_WIDTH-1:DATA_WIDTH]),  //Use the upper bits of the word
    .acc_valid(channel_2_acc_valid),
    .acc_out(channel_2_acc),
    .element(band_counter),
    .element_out(channel_2_element_out)
  );



endmodule