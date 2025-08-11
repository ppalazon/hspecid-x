
import hsid_pkg::*;

module hsid_mse_comp_sva #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Number of bits for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    // Input mse data
    input logic clear,
    input logic mse_in_valid,
    input logic mse_in_of,
    input logic [WORD_WIDTH-1:0] mse_in_value,
    input logic [HSP_LIBRARY_WIDTH-1:0] mse_in_ref,

    // Output mse data
    input logic mse_out_valid,
    input logic [WORD_WIDTH-1:0] mse_min_value,
    input logic [HSP_LIBRARY_WIDTH-1:0] mse_min_ref,
    input logic mse_min_changed,
    input logic [WORD_WIDTH-1:0] mse_max_value,
    input logic [HSP_LIBRARY_WIDTH-1:0] mse_max_ref,
    input logic mse_max_changed
  );

  // Activate output valid signal after input valid signal
  property activate_out_valid;
    @(posedge clk) disable iff (!rst_n || clear) !clear && mse_in_valid |-> ##1 mse_out_valid;
  endproperty

  assert property (activate_out_valid) else $error("Output valid signal not activated after input valid signal");
  cover property (activate_out_valid); // $display("Checked: Output valid signal is activated after input valid signal");

  property deactivate_out_valid;
    @(posedge clk) disable iff (!rst_n || clear) !mse_in_valid |-> ##1 !mse_out_valid;
  endproperty

  assert property (deactivate_out_valid) else $error("Output valid signal not deactivated when input valid signal is low");
  cover property (deactivate_out_valid); // $display("Checked: Output valid signal is deactivated when input valid signal is low");

  // If mse_of is high, there shouldn't be any change in min and max values
  property no_change_on_overflow;
    @(posedge clk) disable iff (!rst_n || clear) mse_in_of |-> ##1 !mse_min_changed && !mse_max_changed;
  endproperty

  assert property (no_change_on_overflow) else $error("Min and max values changed when overflow is high");
  cover property (no_change_on_overflow); // $display("Checked: Min and max values do not change when overflow is high");

  // If input is bigger than min, min should not change
  property min_not_changed_on_bigger_input;
    @(posedge clk) disable iff (!rst_n || clear) !clear && mse_in_valid && !mse_in_of && mse_in_value > mse_min_value |-> ##1
      !mse_min_changed && $stable(mse_min_ref) && $stable(mse_min_value);
  endproperty

  assert property (min_not_changed_on_bigger_input) else $error("Min value changed when input is bigger than min");
  cover property (min_not_changed_on_bigger_input); // $display("Checked: Min value does not change when input is bigger than min");

  // If input is smaller than min, min should change
  property min_changed_on_smaller_input;
    @(posedge clk) disable iff (!rst_n || clear) mse_in_valid && !mse_in_of && mse_in_value < mse_min_value |-> ##1
      mse_min_changed && mse_min_ref == $past(mse_in_ref) && mse_min_value == $past(mse_in_value);
  endproperty

  assert property (min_changed_on_smaller_input) else $error("Min value did not change when input is smaller than min");
  cover property (min_changed_on_smaller_input); // $display("Checked: Min value changes when input is smaller than min");

  // If input is smaller than max, max should not change
  property max_not_changed_on_smaller_input;
    @(posedge clk) disable iff (!rst_n || clear) mse_in_valid && !mse_in_of && mse_in_value < mse_max_value |-> ##1
      !mse_max_changed && $stable(mse_max_ref) && $stable(mse_max_value);
  endproperty

  assert property (max_not_changed_on_smaller_input) else $error("Max value changed when input is smaller than max");
  cover property (max_not_changed_on_smaller_input); // $display("Checked: Max value does not change when input is smaller than max");

  // If input is bigger than max, max should change
  property max_changed_on_bigger_input;
    @(posedge clk) disable iff (!rst_n || clear) !clear && mse_in_valid && !mse_in_of && mse_in_value > mse_max_value |-> ##1
      mse_max_changed && mse_max_ref == $past(mse_in_ref) && mse_max_value == $past(mse_in_value);
  endproperty

  assert property (max_changed_on_bigger_input) else $error("Max value did not change when input is bigger than max");
  cover property (max_changed_on_bigger_input); // $display("Checked: Max value changes when input is bigger than max");

  // On clear, all values should reset
  property clear_resets_to_def_values;
    @(posedge clk) disable iff (!rst_n) clear |-> ##1
      !mse_out_valid && !mse_min_changed && !mse_max_changed &&
      mse_min_value == {WORD_WIDTH{1'b1}} && mse_min_ref == {HSP_LIBRARY_WIDTH{1'b0}} &&
      mse_max_value == {WORD_WIDTH{1'b0}} && mse_max_ref == {HSP_LIBRARY_WIDTH{1'b0}};
  endproperty

  assert property (clear_resets_to_def_values) else $error("Values not reset to default values on clear");
  cover property (clear_resets_to_def_values); // $display("Checked: Values reset on clear

endmodule