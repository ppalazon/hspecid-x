`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_sq_df_acc_sva #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC//, // Data width for accumulator, larger than DATA_WIDTH
    // parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library size
  ) (
    input logic clk,
    input logic rst_n,

    input logic clear,

    input logic initial_acc_en, // Enable initial accumulator value
    input logic [DATA_WIDTH_ACC-1:0] initial_acc, // Initial accumulator value

    input logic data_in_valid, // Valid input values
    input logic [DATA_WIDTH-1:0] data_in_a, // Input vector 1
    input logic [DATA_WIDTH-1:0] data_in_b, // Input vector 2
    input logic data_in_last,
    // input logic [HSP_LIBRARY_WIDTH-1:0] data_in_ref, // Reference vector for sum

    input logic acc_valid, // Output enable signal
    input logic [DATA_WIDTH_ACC-1:0] acc_value, // Output result
    input logic acc_last, // Output band counter
    // input logic [HSP_LIBRARY_WIDTH-1:0] acc_ref, // Reference vector for sum
    input logic acc_of, // Output overflow flag,

    // Internal signals for verification
    input logic stage_1_en, stage_2_en,
    input logic acc_1_en, acc_2_en
    ,
    input logic signed [DATA_WIDTH:0] diff,
    input logic [DATA_WIDTH_MUL-1:0] mult,
    input logic [DATA_WIDTH_ACC:0] acc_w_of
  );

  // Enable stages when data is valid
  property stage_enable;
    @(posedge clk) disable iff (!rst_n || clear) !clear && data_in_valid |-> ##1 stage_1_en ##1 stage_2_en;
  endproperty

  assert property (stage_enable) else $error("Pipeline stages are enabled in sequence");
  cover property (stage_enable); // $display("Checked: Pipeline stages are enabled in sequence");

  // Disable stages when no data is valid
  property stage_disable;
    @(posedge clk) disable iff (!rst_n) !data_in_valid |-> ##1 !stage_1_en ##1 !stage_2_en;
  endproperty

  assert property (stage_disable) else $error("Pipeline stages are disabled in sequence");
  cover property (stage_disable); // $display("Checked: Pipeline stages are disabled in sequence");

  // Propagate the last flag and reference vector through stages
  property propagate_last;
    @(posedge clk) disable iff (!rst_n || clear) data_in_valid |-> ##3 acc_last == $past(data_in_last, 3);
  endproperty

  assert property (propagate_last) else $error("Last flag is propagated correctly through stages");
  cover property (propagate_last); // $display("Checked: Last flag is propagated correctly through stages");

  // Disable stages on clear signal
  property disable_stages_on_clear;
    @(posedge clk) disable iff (!rst_n) clear |-> ##1
      !stage_1_en && !stage_2_en && !acc_valid && !acc_of &&
      acc_value == '0 && acc_last == 1'b0;
  endproperty

  assert property (disable_stages_on_clear) else $error("Stages are disabled on clear signal");
  cover property (disable_stages_on_clear); // $display("Checked: Stages are disabled on clear signal");

  // Compute diff in the same clock cycle as data_in_a and data_in_b
  property compute_diff;
    @(posedge clk) disable iff (!rst_n || clear) !clear && data_in_valid |-> ##1
      diff == $past(data_in_a) - $past(data_in_b);
  endproperty

  assert property (compute_diff) else $error("Difference is computed in the same clock cycle as inputs: diff = %0h != %0h", diff, $past(data_in_a) - $past(data_in_b));
  cover property (compute_diff); // $display("Checked: Difference is computed in the same clock cycle as inputs");

  // Assert multiplication result is correct
  property compute_mult;
    @(posedge clk) disable iff (!rst_n || clear) !clear && data_in_valid |-> ##2
      mult == (($past(data_in_a, 2) - $past(data_in_b, 2)) * ($past(data_in_a, 2) - $past(data_in_b, 2)));
  endproperty

  assert property (compute_mult) else $error("Multiplication result is correct: mult = %0h != %0h", mult, (($past(data_in_a, 2) - $past(data_in_b, 2)) * ($past(data_in_a, 2) - $past(data_in_b, 2))));
  cover property (compute_mult); // $display("Checked: Multiplication result is correct");

  // Assert initial accumulator value is set correctly
  property initial_acc_value;
    @(posedge clk) disable iff (!rst_n || clear) data_in_valid && initial_acc_en |-> ##3
      acc_value == $past(initial_acc, 3) + $past(mult);
  endproperty

  assert property (initial_acc_value) else $error("Initial accumulator value is set correctly: acc_value = %0h != %0h", acc_value, $past(initial_acc, 3) + $past(mult));
  cover property (initial_acc_value); // $display("Checked: Initial accumulator value is set correctly");

  // Assert keep accumulating when initial accumulator is not enabled
  property accumulate_without_initial;
    @(posedge clk) disable iff (!rst_n || clear) data_in_valid && !initial_acc_en |-> ##3
      acc_value == $past(acc_value) + $past(mult);
  endproperty

  assert property (accumulate_without_initial) else $error("Accumulator keeps accumulating when initial accumulator is not enabled: acc_value = %0h != %0h", acc_value, $past(acc_value) + $past(mult));
  cover property (accumulate_without_initial); // $display("Checked: Accumulator keeps accumulating when initial accumulator is not enabled");

  // Assert acc_valid is asserted after at least 4 cycles data_in_last is high
  property acc_valid_after_last;
    @(posedge clk) disable iff (!rst_n || clear) data_in_valid && data_in_last |-> ##3 acc_valid;
  endproperty

  assert property (acc_valid_after_last) else $error("Accumulator valid signal is low after 4 cycles since data_in_last is high");
  cover property (acc_valid_after_last); // $display("Checked: Accumulator valid signal is asserted after data_in_last is high");

  // Assert overflow as soon as its detected
  property acc_of_detected;
    @(posedge clk) disable iff (!rst_n || clear) !acc_2_en && acc_w_of[DATA_WIDTH_ACC] |-> ##1 acc_of;
  endproperty
  assert property (acc_of_detected) else $error("Overflow is detected as soon as it happens: acc_of = %0b != %0b", acc_of, acc_w_of[DATA_WIDTH_ACC]);
  cover property (acc_of_detected); // $display("Checked: Overflow is detected as soon as it happens");

  // Keep overflow flag even though the overflow bit has been overflown, it's difficult to test because it requires a large number of iterations
  property keep_overflow_flag;
    @(posedge clk) disable iff (!rst_n || clear) !acc_2_en && acc_of && !acc_w_of[DATA_WIDTH_ACC] |-> ##1 acc_of;
  endproperty

  assert property (keep_overflow_flag) else $error("Overflow flag is kept even though the overflow bit has been overflown");
  // cover property (keep_overflow_flag); // $display("Checked: Overflow flag is kept even though the overflow bit has been overflown");

  // Avoid changing diff, mult and acc_w_of when no data is valid
  property no_change_when_no_data;
    @(posedge clk) disable iff (!rst_n || clear) !clear && !data_in_valid |-> ##1
      $stable(diff) ##1 $stable(mult) ##1 $stable(acc_w_of);
  endproperty
  assert property (no_change_when_no_data) else $error("No change in diff, mult and acc_w_of when no data is valid");
  cover property (no_change_when_no_data); // $display("Checked: No change in diff, mult and acc_w_of when no data is valid");

endmodule