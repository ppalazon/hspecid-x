`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_sq_df_acc_sva #(
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than DATA_WIDTH
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH // Address width for HSI library size
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
    input logic [HSP_LIBRARY_WIDTH-1:0] data_in_ref, // Reference vector for sum

    input logic acc_valid, // Output enable signal
    input logic [DATA_WIDTH_ACC-1:0] acc_value, // Output result
    input logic acc_last, // Output band counter
    input logic [HSP_LIBRARY_WIDTH-1:0] acc_ref, // Reference vector for sum
    input logic acc_of, // Output overflow flag,

    // Internal signals for verification
    input logic stage_1_en, stage_2_en, stage_3_en,
    input logic acc_1_en, acc_2_en,
    input logic [DATA_WIDTH_ACC-1:0] acc_1, acc_2, acc_3,
    input logic last_1, last_2, last_3,
    input logic [HSP_LIBRARY_WIDTH-1:0] ref_1, ref_2, ref_3,
    input logic acc_of_3,

    input logic signed [DATA_WIDTH:0] diff,
    input logic [DATA_WIDTH_MUL-1:0] mult
  );

  // Invalidate the accumulator on overflow
  property invalidate_on_overflow;
    @(posedge clk) disable iff (!rst_n) acc_of || acc_of_3 |-> ##1 !acc_valid;
  endproperty

  assert property (invalidate_on_overflow) else $error("Accumulator is invalidated on overflow");
  cover property (invalidate_on_overflow); // $display("Checked: Accumulator is invalid after overflow");

  // Enable stages when data is valid
  property stage_enable;
    @(posedge clk) disable iff (!rst_n) data_in_valid |-> ##1 stage_1_en ##1 stage_2_en ##1 stage_3_en;
  endproperty

  assert property (stage_enable) else $error("Pipeline stages are enabled in sequence");
  cover property (stage_enable); // $display("Checked: Pipeline stages are enabled in sequence");

  // Disable stages when no data is valid
  property stage_disable;
    @(posedge clk) disable iff (!rst_n) !data_in_valid |-> ##1
      !stage_1_en ##1 !stage_2_en ##1 !stage_3_en;
  endproperty

  assert property (stage_disable) else $error("Pipeline stages are disabled in sequence");
  cover property (stage_disable); // $display("Checked: Pipeline stages are disabled in sequence");

  // Propagate the last flag and reference vector through stages
  property propagate_last_and_ref;
    @(posedge clk) disable iff (!rst_n) data_in_valid |-> ##4
      acc_last == $past(data_in_last, 4) && acc_ref == $past(data_in_ref, 4);
  endproperty

  assert property (propagate_last_and_ref) else $error("Last flag is propagated correctly through stages");
  cover property (propagate_last_and_ref); // $display("Checked: Last flag is propagated correctly through stages");

  // Disable stages on clear signal
  property disable_stages_on_clear;
    @(posedge clk) disable iff (!rst_n) clear |-> ##1
      !stage_1_en && !stage_2_en && !stage_3_en && !acc_valid;
  endproperty

  assert property (disable_stages_on_clear) else $error("Stages are disabled on clear signal");
  cover property (disable_stages_on_clear); // $display("Checked: Stages are disabled on clear signal");

  // Compute diff in the same clock cycle as data_in_a and data_in_b
  property compute_diff;
    @(posedge clk) disable iff (!rst_n) data_in_valid |-> ##1
      diff == $past(data_in_a) - $past(data_in_b);
  endproperty

  assert property (compute_diff) else $error("Difference is computed in the same clock cycle as inputs: diff = %0h != %0h", diff, $past(data_in_a) - $past(data_in_b));
  cover property (compute_diff); // $display("Checked: Difference is computed in the same clock cycle as inputs");

  // Assert multiplication result is correct
  property compute_mult;
    @(posedge clk) disable iff (!rst_n) data_in_valid |-> ##2
      mult == (($past(data_in_a, 2) - $past(data_in_b, 2)) * ($past(data_in_a, 2) - $past(data_in_b, 2)));
  endproperty

  assert property (compute_mult) else $error("Multiplication result is correct: mult = %0h != %0h", mult, (($past(data_in_a, 2) - $past(data_in_b, 2)) * ($past(data_in_a, 2) - $past(data_in_b, 2))));
  cover property (compute_mult); // $display("Checked: Multiplication result is correct");

  // Assert initial accumulator value is set correctly
  property initial_acc_value;
    @(posedge clk) disable iff (!rst_n) data_in_valid && initial_acc_en |-> ##3
      acc_3 == $past(initial_acc, 3) + $past(mult);
  endproperty

  assert property (initial_acc_value) else $error("Initial accumulator value is set correctly: acc_3 = %0h != %0h", acc_3, $past(initial_acc, 3) + $past(mult));
  cover property (initial_acc_value); // $display("Checked: Initial accumulator value is set correctly");

  // Assert keep accumulating when initial accumulator is not enabled
  property accumulate_without_initial;
    @(posedge clk) disable iff (!rst_n) data_in_valid && !initial_acc_en |-> ##3
      acc_3 == $past(acc_3) + $past(mult);
  endproperty

  assert property (accumulate_without_initial) else $error("Accumulator keeps accumulating when initial accumulator is not enabled: acc_3 = %0h != %0h", acc_3, $past(acc_3) + $past(mult));
  cover property (accumulate_without_initial); // $display("Checked: Accumulator keeps accumulating when initial accumulator is not enabled");


endmodule