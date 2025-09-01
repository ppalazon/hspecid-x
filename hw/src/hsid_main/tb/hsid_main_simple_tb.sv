`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_main_simple_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than DATA_WIDTH
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Number of bits for Hyperspectral Pixels (8 bits - 256 bands)
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,  // Number of bits for Hyperspectral Pixels Library (11 bits - 4096 pixels)
    parameter BUFFER_WIDTH = HSID_FIFO_ADDR_WIDTH  // Length of the buffer
  ) ();

  reg clk;
  reg rst_n;
  reg band_data_in_valid;
  reg [WORD_WIDTH-1:0] band_data_in;
  reg [HSP_LIBRARY_WIDTH-1:0] hsp_library_size_in;
  reg [HSP_BANDS_WIDTH-1:0] hsp_bands_in;  // HSP bands to process
  wire [HSP_LIBRARY_WIDTH-1:0] mse_min_ref;
  wire [HSP_LIBRARY_WIDTH-1:0] mse_max_ref;
  wire [WORD_WIDTH-1:0] mse_min_value;
  wire [WORD_WIDTH-1:0] mse_max_value;

  // Block interface for handshake signals
  reg start;
  reg clear;  // Clear signal to reset MSE values
  wire done;
  wire idle;
  wire ready;
  wire error;
  wire cancelled;

  // DUT instantiation
  hsid_main #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .BUFFER_WIDTH(BUFFER_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .band_data_in_valid(band_data_in_valid),
    .band_data_in(band_data_in),
    .hsp_library_size_in(hsp_library_size_in),
    .hsp_bands_in(hsp_bands_in),
    .mse_min_ref(mse_min_ref),
    .mse_max_ref(mse_max_ref),
    .mse_min_value(mse_min_value),
    .mse_max_value(mse_max_value),
    .clear(clear),
    .start(start),
    .done(done),
    .idle(idle),
    .ready(ready),
    .error(error),
    .cancelled(cancelled)
  );

  // Constraint randomization for the HSI vector
  HsidMainGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_main_gen = new();

  HsidHSPReferenceGen #(
    .DATA_WIDTH(DATA_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH)
  ) hsid_hsp_ref_gen = new();

  // Test vectors
  logic [DATA_WIDTH-1:0] captured_hsp [];
  logic [DATA_WIDTH-1:0] library_hsp [][];
  logic [DATA_WIDTH_ACC:0] acc_int [][];
  logic [WORD_WIDTH-1:0] expected_mse [];
  logic expected_mse_of [];

  logic [WORD_WIDTH-1:0] min_mse_value_expected;
  logic [WORD_WIDTH-1:0] max_mse_value_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] min_mse_ref_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] max_mse_ref_expected;

  int hsp_band_packs = 0;
  logic [WORD_WIDTH-1:0] hsp_packed [];

// Count for the number of inserted band packs
  int count_insert;
  logic insert_en;

// Waveform generation for debugging
  initial begin : tb_waveform
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_main_simple_tb);
  end

  initial begin : tb_hsid_main
    clk = 1;
    rst_n = 1;
    band_data_in_valid = 0;
    band_data_in = 0;
    hsp_bands_in = '0;
    hsp_library_size_in = 0;
    start = 0;
    clear = 0;

    // Reset the DUT
    #3 rst_n = 0;
    #5 rst_n = 1;  // Release reset

    $display("Case 1: Simple operation");

    captured_hsp = '{0,1,2,3,4,5,6,7,8,9};  // Get the measure vector
    library_hsp = new [2];
    acc_int = new [2];
    expected_mse = new [2];
    expected_mse_of = new [2];
    hsp_band_packs = (10 + 1) / 2;

    library_hsp[0] = '{7,2,2,6,1,7,5,7,3,9};  // Library vector 0
    library_hsp[1] = '{6,1,6,8,2,5,4,2,3,0};  // Library vector 1

    $display(" - Captured HSP: %p", captured_hsp);
    $display(" - Library HSP 0: %p", library_hsp[0]);
    $display(" - Library HSP 1: %p", library_hsp[1]);

    // Generate random library vectors
    hsid_main_gen.hsp_bands = 10;
    hsid_main_gen.library_size = 2;
    hsid_main_gen.initial_acc = 0;
    hsid_main_gen.test_rnd_insert = 0;
    for (int i = 0; i < 2; i++) begin : generate_library
      hsid_main_gen.sq_df_acc_vctr(captured_hsp, library_hsp[i], acc_int[i]);
      $display(" - Accumulated int for library vector %0d: %p", i, acc_int[i]);
      hsid_main_gen.mse(acc_int[i], expected_mse[i], expected_mse_of[i]);
    end

    // Compute expected min and max MSE values and references
    hsid_main_gen.min_max_mse(expected_mse,
      min_mse_value_expected, max_mse_value_expected,
      min_mse_ref_expected, max_mse_ref_expected);

    $display(" - Expected min MSE: %0d, ref: %0d", min_mse_value_expected, min_mse_ref_expected);
    $display(" - Expected max MSE: %0d, ref: %0d", max_mse_value_expected, max_mse_ref_expected);

    // Start the DUT
    a_bef_start_idle: assert (idle == 1) else $error("DUT is not idle at start");
    a_bef_start_done: assert (done == 0) else $error("DUT is done before starting");
    a_bef_start_rdy: assert (ready == 0) else $error("DUT is ready before starting");

    start = 1;
    #10;

    // Configure the DUT
    start = 0;
    hsp_library_size_in = 2;
    hsp_bands_in = 10;

    a_conf_idle: assert (idle == 0) else $error("DUT is idle on configuration");
    a_conf_done: assert (done == 0) else $error("DUT is done on configuration");
    a_conf_rdy: assert (ready == 0) else $error("DUT is ready on configuration");

    #10;
    hsp_library_size_in = '0;
    hsp_bands_in = '0;

    a_read_cap_idle: assert (idle == 0) else $error("DUT is idle on reading captured hsp");
    a_read_cap_done: assert (done == 0) else $error("DUT is done on reading captured hsp");
    a_read_cap_rdy: assert (ready == 1) else $error("DUT is not ready on reading captured hsp");

    // Send the captured vector (packed)
    $display(" - Sending captured vector...");
    hsid_main_gen.band_packer(captured_hsp, hsp_packed);
    count_insert = 0;
    while (count_insert < hsp_band_packs) begin
      insert_en = hsid_main_gen.test_rnd_insert ? $urandom % 2 : 1; // Randomly enable or disable element processing
      band_data_in = hsp_packed[count_insert];
      band_data_in_valid = insert_en;
      #10;
      a_insert_cap: assert (ready == 1) else $fatal(0, "DUT is not ready to accept input, check if you are sending all band packs");
      if (insert_en) count_insert++;
    end

    band_data_in_valid = 0;  // Disable input vector valid signal
    band_data_in = 0;  // Reset input vector
    #10;

    a_read_lib_idle: assert (idle == 0) else $error("DUT is idle on reading library");
    a_read_lib_done: assert (done == 0) else $error("DUT is done on reading library");
    a_read_lib_rdy: assert (ready == 1) else $error("DUT is not ready on reading library");

    $display(" - Sending library vectors...");
    // Send the library vectors
    for (int i = 0; i < 2; i++) begin
      hsid_main_gen.band_packer(library_hsp[i], hsp_packed);
      count_insert = 0;
      // $display("  - Sending library vector: %p", hsp_packed);
      while (count_insert < hsp_band_packs) begin
        insert_en = hsid_main_gen.test_rnd_insert ? $urandom % 2 : 1; // Randomly enable or disable element processing
        band_data_in = hsp_packed[count_insert];
        band_data_in_valid = insert_en;
        // $display("     - Sending band pack %0d of %0d hsp: %h", count_insert, i, band_data_in);
        #10;
        if (!(i == 2 - 1 && count_insert == hsp_band_packs - 1)) begin
          a_insert_lib: assert (ready == 1) else $fatal(0, "DUT is not ready to accept input, check if you are sending all band packs");
        end
        if (insert_en) count_insert++;
      end
    end

    band_data_in_valid = 0;  // Disable input vector valid signal
    band_data_in = 0;  // Reset input vector

    $display(" - Waiting 8 cycles to finish processing (2 to write and read fifo, 5 mse, 1 change state)...");
    #80;

    a_finish_done: assert (done == 1) else $error("DUT is not done after processing, you should check waiting cycles");
    a_finish_idle: assert (idle == 0) else $error("DUT is idle after processing");
    a_finish_rdy: assert (ready == 0) else $error("DUT is ready after processing");

    // wait(done);  // Wait for the DUT to finish processing
    // $display("DUT is done processing");

    // Check the results
    a_mse_min_value: assert (mse_min_value == min_mse_value_expected) else
      $error("Minimum MSE value is incorrect: expected %0d, got %0d", min_mse_value_expected, mse_min_value);
    a_mse_max_value: assert (mse_max_value == max_mse_value_expected) else
      $error("Maximum MSE value is incorrect: expected %0d, got %0d", max_mse_value_expected, mse_max_value);
    a_mse_min_ref: assert (mse_min_ref == min_mse_ref_expected) else
      $error("Minimum MSE reference is incorrect: expected %0d, got %0d", min_mse_ref_expected, mse_min_ref);
    a_mse_max_ref: assert (mse_max_ref == max_mse_ref_expected) else
      $error("Maximum MSE reference is incorrect: expected %0d, got %0d", max_mse_ref_expected, mse_max_ref);

    #10;

    a_aft_finish_idle: assert (idle == 1) else $error("DUT is not idle after processing");
    a_aft_finish_done: assert (done == 0) else $error("DUT is done after processing");
    a_aft_finish_rdy: assert (ready == 0) else $error("DUT is ready after processing");

    $finish;
  end

// initial begin
//   #2000; $finish;  // Timeout to prevent infinite simulation
// end

  always
    #5 clk = ! clk;

endmodule