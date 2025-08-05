`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_main_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than DATA_WIDTH
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Number of bits for Hyperspectral Pixels (8 bits - 256 bands)
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,  // Number of bits for Hyperspectral Pixels Library (11 bits - 4096 pixels)
    parameter BUFFER_WIDTH = HSID_FIFO_ADDR_WIDTH  // Length of the buffer
  ) ();

  localparam MAX_WORD = {WORD_WIDTH{1'b1}};
  localparam MAX_HSP_BANDS = {HSP_BANDS_WIDTH{1'b1}};
  localparam MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}};

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
    .error(error)
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

  HsidMainRandom #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_main_random = new();

  // Covergroup to coverage the MSE values
  covergroup hsid_main_cg @(posedge clk);
    coverpoint band_data_in_valid;
    coverpoint band_data_in iff (band_data_in_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins mid = {[1:MAX_WORD-1]};
    }
    coverpoint hsp_bands_in {
      bins min = {7};
      bins max = {MAX_HSP_BANDS};
      bins mid = {[1:MAX_HSP_BANDS-1]};
    }
    coverpoint hsp_library_size_in{
      bins min = {1};
      bins max = {MAX_HSP_LIBRARY};
      bins mid = {[1:MAX_HSP_LIBRARY-1]};
    }
    coverpoint clear;
  endgroup

  hsid_main_cg hsid_main_cov = new();

  // Binding SVA assertions to the DUT
  bind hsid_main_fsm hsid_main_fsm_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_main_fsm_sva_inst (.*);

  bind hsid_mse hsid_mse_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_mse_sva_inst (.*);

  bind hsid_sq_df_acc hsid_sq_df_acc_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC)
  ) hsid_sq_df_acc_sva_inst (.*);

  bind hsid_mse_comp hsid_mse_comp_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_mse_comp_sva_inst (.*);

  bind hsid_fifo hsid_fifo_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) hsid_fifo_sva_inst (.*);

  // bind hsid_fifo hsid_fifo_sva #(
  //   .DATA_WIDTH(WORD_WIDTH),
  //   .FIFO_ADDR_WIDTH(HSP_BANDS_WIDTH)
  // ) hsid_fifo_sva_inst (.*);

  // Test vectors
  logic [DATA_WIDTH-1:0] captured [];
  logic [DATA_WIDTH-1:0] lib [][];
  logic [DATA_WIDTH_ACC:0] acc_int [][];
  logic [WORD_WIDTH-1:0] expected_mse [];
  logic expected_mse_of [];

  logic [WORD_WIDTH-1:0] min_mse_value_expected;
  logic [WORD_WIDTH-1:0] max_mse_value_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] min_mse_ref_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] max_mse_ref_expected;

  int hsp_band_packs = 0;
  logic [WORD_WIDTH-1:0] hsp_packed [];
  logic will_raised_error;

// Count for the number of inserted band packs
  int count_insert;
  logic insert_en;

// Waveform generation for debugging
  initial begin : tb_waveform
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_main_tb);
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

    $display("Case 1: Test normal operation with random vectors ...");
    for (int t = 0; t < 20; t++) begin : case_1
      // Generate a random vector as a measure
      if (!hsid_main_gen.randomize()) $fatal(0, "Failed to randomize measure vector");

      $display("Test %0d: Library size: %0d, HSP Bands: %0d, Random Insert: %0d", t, hsid_main_gen.library_size, hsid_main_gen.hsp_bands, hsid_main_gen.test_rnd_insert);
      captured = hsid_main_gen.vctr1;  // Get the measure vector
      lib = new [hsid_main_gen.library_size];
      acc_int = new [hsid_main_gen.library_size];
      expected_mse = new [hsid_main_gen.library_size];
      expected_mse_of = new [hsid_main_gen.library_size];
      hsp_band_packs = (hsid_main_gen.hsp_bands + 1) / 2; // Calculate the number of HSP band packs
      // $display("Captured vector: %p", captured);

      // Generate random library vectors
      lib = new[hsid_main_gen.library_size];
      hsid_hsp_ref_gen.hsp_bands = hsid_main_gen.hsp_bands;
      for (int i = 0; i < hsid_main_gen.library_size; i++) begin : generate_library
        if (!hsid_hsp_ref_gen.randomize()) $fatal(0, "Failed to randomize library vector %0d", i);
        lib[i] = hsid_hsp_ref_gen.reference_hsp;
        hsid_main_gen.sq_df_acc_vctr(captured, lib[i], acc_int[i]); // Get intermediate accumulator values
        hsid_main_gen.mse(acc_int[i], expected_mse[i], expected_mse_of[i]);
        $display("  - Id: %0d, Accumulated value: %p, MSE: %d, Overflow: %0d", i, acc_int[i][hsid_main_gen.hsp_bands-1], expected_mse[i], expected_mse_of[i]);
        // $display("  - Library vector %0d: %p, MSE: %d", i, lib[i], expected_mse[i]);
        // $display("  - Intermediate accumulator %0d: %p", i, acc_int[i]);
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
      hsp_library_size_in = hsid_main_gen.library_size;
      hsp_bands_in = hsid_main_gen.hsp_bands;

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
      hsid_main_gen.band_packer(captured, hsp_packed);
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
      for (int i = 0; i < hsid_main_gen.library_size; i++) begin
        hsid_main_gen.band_packer(lib[i], hsp_packed);
        count_insert = 0;
        // $display("  - Sending library vector: %p", hsp_packed);
        while (count_insert < hsp_band_packs) begin
          insert_en = hsid_main_gen.test_rnd_insert ? $urandom % 2 : 1; // Randomly enable or disable element processing
          band_data_in = hsp_packed[count_insert];
          band_data_in_valid = insert_en;
          // $display("     - Sending band pack %0d of %0d hsp: %h", count_insert, i, band_data_in);
          #10;
          if (!(i == hsid_main_gen.library_size - 1 && count_insert == hsp_band_packs - 1)) begin
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
    end

    $display("Case 2: Send complete random inputs to the DUT, without clear ...");
    for(int i=0; i<300; i++) begin : case_2
      if (!hsid_main_random.randomize()) $fatal(0, "Failed to randomize HSI vector");

      band_data_in = hsid_main_random.band_data_in;
      band_data_in_valid = hsid_main_random.band_data_in_valid;
      hsp_bands_in = hsid_main_random.hsp_bands_in;
      hsp_library_size_in = hsid_main_random.hsp_library_size_in;
      start = hsid_main_random.start;
      clear = '0;

      #10; // Wait for the DUT to process the input
    end

    $display("Case 3: Clear and reset the DUT on different states ...");
    for (int i=0; i<300; i++) begin : case_3
      if (!hsid_main_random.randomize()) $fatal(0, "Failed to randomize HSI vector");

      start = hsid_main_random.start;
      clear = hsid_main_random.clear;
      rst_n = hsid_main_random.rst_n;
      band_data_in = hsid_main_random.band_data_in;
      band_data_in_valid = '1;
      hsp_bands_in = 7; // Minimum HSP bands to avoid errors
      hsp_library_size_in = 1; // Minimal library size to avoid errors

      #10; // Wait for the DUT to process the input
    end

    $display("Case 4: Test error on configuration ...");
    for (int i=0; i<50; i++) begin : case_4
      if (!hsid_main_random.randomize()) $fatal(0, "Failed to randomize HSI vector");

      // Clear
      clear = 1;
      #10;
      clear = 0;
      #10;
      // Start
      start = 1;
      #10;
      start = 0;
      // Configure
      hsp_bands_in = i % 3 == 0 ? '0 : hsid_main_random.hsp_bands_in; // Invalid HSP bands
      hsp_library_size_in = i % 2 ==0 ? '0: hsid_main_random.hsp_library_size_in; // Invalid HSP bands
      will_raised_error = hsp_bands_in == 0 || hsp_library_size_in == 0;
      #10;
      if (will_raised_error)
        a_error: assert (error == 1) else $error("DUT did not raise error on invalid configuration");
      else
        a_non_error: assert (error == 0) else $error("DUT did raise error on valid configuration");
      #30;
    end
    $finish;
  end

// initial begin
//   #2000; $finish;  // Timeout to prevent infinite simulation
// end

  always
    #5 clk = ! clk;

endmodule