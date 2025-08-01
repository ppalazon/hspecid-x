import hsid_pkg::*;

module hsid_mse_sva #(
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
    input logic [HSP_BANDS_WIDTH-1:0] hsp_bands,  // HSP bands to process

    input logic [WORD_WIDTH-1:0] mse_value,  // Output mean square error
    input logic [HSP_LIBRARY_WIDTH-1:0] mse_ref,  // Reference vector for sum
    input logic mse_valid,  // Enable input sample data
    input logic mse_of,
    input logic acc_of,

    // Internal signals for verification
    input logic channel_1_acc_valid, channel_2_acc_valid,
    input logic [DATA_WIDTH_ACC-1:0] channel_1_acc_value, channel_2_acc_value,
    input logic channel_1_acc_last, channel_2_acc_last,
    input logic channel_1_acc_of, channel_2_acc_of,  // Overflow flag for the accumulated vector
    input logic compute_acc_sum_en,  // Enable signal for mean square error accumulator
    input logic compute_mse_en,
    input logic [DATA_WIDTH_ACC:0] acc_value,  // Accumulator for both channels
    input logic [HSP_LIBRARY_WIDTH-1:0] acc_ref,  // Reference vector for mean square error
    input logic [HSP_BANDS_WIDTH-1:0] acc_hsp_bands
  );

  // Assert mse_valid after 5 (3 of sq_df_acc + 2 of mse) clock cycles when band_pack_valid and band_pack_last are high
  property mse_valid_after_band_pack_last;
    @(posedge clk) disable iff (!rst_n || clear) band_pack_last && band_pack_valid |-> ##5 mse_valid;
  endproperty

  assert property (mse_valid_after_band_pack_last) else $error("MSE valid signal is not asserted when expected");
  cover property (mse_valid_after_band_pack_last); // $display("Checked: MSE valid signal is asserted when expected");

  // Safe hsp_bands and vctr_ref values on last band_pack
  property safe_hsp_bands_and_vctr_ref;
    @(posedge clk) disable iff (!rst_n || clear) band_pack_last && band_pack_valid |-> ##1
      (acc_hsp_bands == $past(hsp_bands)) && (acc_ref == $past(vctr_ref)) ##4
      (acc_hsp_bands == $past(hsp_bands, 5)) && (acc_ref == $past(vctr_ref,5));
  endproperty
  assert property (safe_hsp_bands_and_vctr_ref) else $error("HSP bands and vector reference are not safe on last band pack");
  cover property (safe_hsp_bands_and_vctr_ref); // $display("Checked: HSP bands and vector reference are safe on last band pack");

  // If hsp_bands is odd, LSB of band_pack_a and band_pack_b are zeros
  property odd_hsp_bands_lsb_zero;
    @(posedge clk) disable iff (!rst_n) band_pack_last && band_pack_valid && hsp_bands[0] |->
      !$isunknown(band_pack_a[DATA_WIDTH-1:0]) && !$isunknown(band_pack_b[DATA_WIDTH-1:0]);
  endproperty

  assert property (odd_hsp_bands_lsb_zero) else $error("LSB of band_pack_a and band_pack_a are not zero when hsp_bands is odd");
  cover property (odd_hsp_bands_lsb_zero); //$display("LSB of band_pack_a and band_pack_a are zero when hsp_bands is odd")

  // Ensure HSP bands are at least 5, to avoid problems with the latest steps of mse (3 of sq_df_acc + 2 of mse)
  property hsp_bands_bigger_than_five;
    @(posedge clk) disable iff (!rst_n) band_pack_last && band_pack_valid |-> hsp_bands >= 5;
  endproperty

  assert property (hsp_bands_bigger_than_five) else $error("HSP bands are less than 5, which may cause issues in the last steps of MSE");
  cover property (hsp_bands_bigger_than_five); // $display("Checked: HSP bands are greater than or equal to 6");

  // On clear signal, all outputs should be zero
  property clear_outputs;
    @(posedge clk) disable iff (!rst_n) clear |-> ##1
      mse_value == '0 && mse_ref == '0 && mse_valid == 0 && mse_of == 0 && acc_of == 0;
  endproperty

  assert property (clear_outputs) else $error("Outputs are not cleared on clear signal");
  cover property (clear_outputs); // $display("Checked: Outputs are cleared on clear signal");

  // Propagate channel accumulators
  property propagate_acc_of;
    @(posedge clk) disable iff (!rst_n || clear) (channel_1_acc_of || channel_2_acc_of) && channel_1_acc_last |-> ##2 acc_of;
  endproperty

  assert property (propagate_acc_of) else $error("Accumulator overflow flag is not propagated correctly");
  cover property (propagate_acc_of); // $display("Checked: Accumulator overflow flag is propagated correctly");

endmodule