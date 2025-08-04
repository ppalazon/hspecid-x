`timescale 1ns / 1ps

import hsid_pkg::*;

module hsid_mse_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH, // Width of the word in bits
    parameter DATA_WIDTH = HSID_DATA_WIDTH, // Data width for HSP bands
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL, // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC, // Data width for accumulator, larger than WORD_WIDTH
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH, // Address width for HSP bands
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter TEST_LIBRARY_SIZE = 10, // Size of the HSI library to test
    parameter TEST_RND_INSERT = 1, // Enable random insertion of test vectors
    parameter TEST_OVERFLOW = 0 // Enable overflow test
  );

  // Max values
  localparam logic[DATA_WIDTH-1:0]        MAX_DATA = {DATA_WIDTH{1'b1}}; // Maximum value for data vectors
  localparam logic[DATA_WIDTH_ACC-1:0]    MAX_DATA_ACC = {DATA_WIDTH_ACC{1'b1}}; // Maximum value for accumulator, it's wider than 32 bits
  localparam logic[HSP_BANDS_WIDTH-1:0]   MAX_HSP_BANDS = {HSP_BANDS_WIDTH{1'b1}}; // Maximum value for HSP bands
  localparam logic[HSP_LIBRARY_WIDTH-1:0] MAX_HSP_LIBRARY = {HSP_LIBRARY_WIDTH{1'b1}}; // Maximum value for HSI library
  localparam logic[WORD_WIDTH-1:0]        MAX_WORD = {WORD_WIDTH{1'b1}}; // Maximum value for word width

  reg clk;
  reg rst_n;
  reg clear;  // Clear signal to reset MSE values
  reg band_pack_start;
  reg band_pack_last;
  reg [WORD_WIDTH-1:0] band_pack_a;
  reg [WORD_WIDTH-1:0] band_pack_b;
  reg band_pack_valid;
  reg [HSP_LIBRARY_WIDTH-1:0] vctr_ref; // Reference vector for MSE
  reg [HSP_BANDS_WIDTH-1:0] hsp_bands; // HSP bands to process
  wire [WORD_WIDTH-1:0] mse_value;
  wire [HSP_LIBRARY_WIDTH-1:0] mse_ref; // Reference vector for MSE
  wire mse_valid;
  // wire mse_of; // Overflow flag for mean square error
  wire acc_of; // Overflow flag for the accumulated vector

  // DUT instantiation
  hsid_mse #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .clear(clear),
    .band_pack_start(band_pack_start),
    .band_pack_last(band_pack_last),
    .hsp_ref(vctr_ref),
    .band_pack_a(band_pack_a),
    .band_pack_b(band_pack_b),
    .band_pack_valid(band_pack_valid),
    .hsp_bands(hsp_bands),
    .mse_value(mse_value),
    .mse_ref(mse_ref),
    .mse_valid(mse_valid),
    // .mse_of(mse_of),
    .acc_of(acc_of)
  );

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_mse_tb);
  end

  // Coverage group for the MSE module
  covergroup hsid_mse_cg @(posedge clk);
    coverpoint clear;
    coverpoint band_pack_start iff(band_pack_valid);
    coverpoint band_pack_last iff(band_pack_valid);
    coverpoint band_pack_valid;
    coverpoint band_pack_a iff(band_pack_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins middle = {[1:MAX_WORD-1]};
    }
    coverpoint band_pack_b iff(band_pack_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins middle = {[1:MAX_WORD-1]};
    }
    coverpoint vctr_ref iff(band_pack_valid) {
      bins zero = {0};
      bins max = {MAX_HSP_LIBRARY};
      bins middle = {[1:MAX_HSP_LIBRARY-1]};
    }
    coverpoint hsp_bands iff(band_pack_valid) {
      bins min = {7};
      bins max = {MAX_HSP_BANDS};
      bins middle = {[1:MAX_HSP_BANDS-1]};
    }
    coverpoint mse_valid;
    coverpoint mse_value iff(mse_valid) {
      bins zero = {0};
      bins max = {MAX_WORD};
      bins middle = {[1:MAX_WORD-1]};
    }
    coverpoint mse_ref iff(mse_valid) {
      bins zero = {0};
      bins max = {MAX_HSP_LIBRARY};
      bins middle = {[1:MAX_HSP_LIBRARY-1]};
    }
    coverpoint acc_of iff(mse_valid);
  endgroup
  hsid_mse_cg mse_cg = new();

  // Constrained random class to generate test vectors
  HsidHSPixelMseGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsp_mse_gen = new();

  HsidMSERandom #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsp_mse_complete_gen = new();

  // Binding SVA assertions to the MSE module
  bind hsid_mse hsid_mse_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) dut_sva (.*);

  // Test vectors
  int mse_order = 0;
  int hsp_band_packs = 0;
  int mse_pipeline = 4; // Number of clock cycles to wait for MSE calculation
  int overflow_sends; // Count of overflow occurrences
  logic [WORD_WIDTH-1:0] vctr1 [];
  logic [WORD_WIDTH-1:0] vctr2 [];
  logic [HSP_LIBRARY_WIDTH-1:0] exp_id [TEST_LIBRARY_SIZE];
  logic [WORD_WIDTH-1:0] exp_mse [TEST_LIBRARY_SIZE];
  // logic exp_mse_of [TEST_LIBRARY_SIZE];
  logic exp_acc_of [TEST_LIBRARY_SIZE];
  logic [DATA_WIDTH_ACC:0] acc_inter [TEST_LIBRARY_SIZE][];

  // Random value
  int count_insert = 0;

  // Check mse_of and acc_of values
  logic [63:0] max_possible_acc;
  logic [63:0] max_possible_divisor;

  initial begin
    clk = 1;
    rst_n = 1;
    clear = 0;
    band_pack_start = 0;
    band_pack_last = 0; // Not used in this test, but required by the DUT
    band_pack_a = 0;
    band_pack_b = 0;
    band_pack_valid = 0;
    vctr_ref = 0;

    #3 rst_n = 0;  // Reset the DUT
    #5 rst_n = 1;  // Release reset

    $display("Case 0: Check whether it's possible to get a real 'mse_of' or 'acc_of' with this configuration...");
    $display("DATA_WIDTH: %0d, DATA_WIDTH_MUL: %0d, DATA_WIDTH_ACC: %0d", DATA_WIDTH, DATA_WIDTH_MUL, DATA_WIDTH_ACC);
    for (int i=0; i<MAX_HSP_BANDS; i++) begin
      max_possible_acc = i * (MAX_DATA * MAX_DATA);
      max_possible_divisor = i * MAX_WORD;
      if ($clog2(max_possible_acc) > DATA_WIDTH_ACC) begin
        $display("You need bits %0d to store max possible acc %0h without overflow to hold pixels of %0d, but you have %0d bits ", $clog2(max_possible_acc), max_possible_acc, i, DATA_WIDTH_ACC);
      end
      if (max_possible_acc > max_possible_divisor) begin
        $display("You could get mse_of with %0d bands, because max possible acc %0h is larger than max possible divisor %0h", i, max_possible_acc, max_possible_divisor);
      end
    end

    $display("Case 1: Testing with random values...");
    for (int i=0; i<TEST_LIBRARY_SIZE; i++) begin
      // Generate random vectors
      if (hsp_mse_gen.randomize()) begin
        hsp_mse_gen.band_packer(hsp_mse_gen.vctr1, vctr1);
        hsp_mse_gen.band_packer(hsp_mse_gen.vctr2, vctr2);
        hsp_mse_gen.sq_df_acc_vctr(hsp_mse_gen.vctr1, hsp_mse_gen.vctr2, acc_inter[i]);
        hsp_mse_gen.mse(acc_inter[i], exp_mse[i], exp_acc_of[i]); // exp_mse_of[i]
        exp_id[i] = hsp_mse_gen.vctr_ref;

        hsp_band_packs = (hsp_mse_gen.hsp_bands + 1) / 2; // Number of HSP band packs, each pack contains two bands

        $display("Test %0d: Id: %0d, Bands: %0d, Expected MSE: %0d, Expected acc_of: %0d", i, hsp_mse_gen.vctr_ref, hsp_mse_gen.hsp_bands, exp_mse[i], exp_acc_of[i]);
        // $display("Test %0d: Vctr1: %p", i, hsp_mse_gen.vctr1);
        // $display("Test %0d: Vctr2: %p", i, hsp_mse_gen.vctr2);
        // $display("Test %0d: Intermediate Accumulated: %p", i, acc_inter[i]);

        // Start processing the vectors
        hsp_bands = hsp_mse_gen.hsp_bands; // Set the number of HSP bands to process
        vctr_ref = hsp_mse_gen.vctr_ref; // Set the reference vector for MSE

        // Assert initial accumulator value is zero
        a_init_acc: assert (hsp_mse_gen.initial_acc == 0) else $fatal(0, "Initial accumulator value is not zero");

        count_insert = 0;

        while (count_insert < hsp_band_packs) begin
          band_pack_valid = TEST_RND_INSERT ? $urandom % 2: 1; // Randomly enable or disable element processing
          if (count_insert == 0) begin
            band_pack_start = 1; // Start the vector processing
          end else begin
            band_pack_start = 0;
          end
          if (count_insert == hsp_band_packs - 1) begin
            band_pack_last = 1;
          end else begin
            band_pack_last = 0;
          end
          band_pack_a = vctr1[count_insert];
          band_pack_b = vctr2[count_insert];
          #10; // Wait for a clock cycle

          if(mse_valid) begin
            check_mse(); // Check the MSE values
          end

          if (band_pack_valid) begin
            count_insert++;
          end
        end
        band_pack_valid = 0;
      end else begin
        $display("Failed to randomize vectors");
      end
    end

    #(10*(mse_pipeline)); // Wait for the last MSE calculation to complete
    check_mse();

    $display("Expected MSE values: %p", exp_mse);

    #10;
    a_all_mse_checked: assert (mse_order == TEST_LIBRARY_SIZE) else $fatal(0, "Not all MSE values were checked");

    $display("Case 2: Clear signal test...");
    clear = 1; // Set clear signal to reset MSE values
    #10; // Wait for a clock cycle
    clear = 0; // Clear signal is deasserted
    #10;

    $display("Case 3: Setting same values for both vectors...");
    // Test case to reach overflow in the accumulator
    if(!hsp_mse_gen.randomize()) $fatal(0, "Not valid randomization"); // Randomize the vectors
    hsp_mse_gen.band_packer(hsp_mse_gen.vctr1, vctr1);
    hsp_band_packs = (hsp_mse_gen.hsp_bands + 1) / 2;
    for(int i=0; i<hsp_band_packs; i++) begin
      band_pack_valid = 1; // Enable input sample data
      band_pack_start = (i == 0); // Enable initial accumulator value on first element
      band_pack_last = (i == hsp_band_packs - 1); // Set last flag for the last element
      band_pack_a = vctr1[i]; // Use maximum value for the word
      band_pack_b = vctr1[i]; // Use zero for the second word to get maximum difference
      hsp_bands = hsp_mse_gen.hsp_bands; // Set maximum HSP bands
      vctr_ref = hsp_mse_gen.vctr_ref; // Set maximum reference vector
      #10; // Wait for a clock cycle
    end

    // Disable input sample data
    band_pack_valid = 0;

    #(10 * mse_pipeline); // Wait for the last MSE calculation to complete
    a_zero_acc_of_valid: assert (mse_valid) else $fatal(0, "MSE valid signal is not asserted after zero test, please check pipeline waiting cycles");
    a_zerp_acc_of: assert (!acc_of) else $error("Accumulator overflow flag is set after zero test");
    // a_zero_mse_of: assert (!mse_of) else $error("MSE overflow flag is set after zero test");
    a_zero_acc_value: assert (mse_value == '0) else $error("Accumulator value is not as we expected after zero test, got %0h", mse_value);


    $display("Case 4: Reaching maximum values for accumulator and mse...");
    // Test case to reach overflow in the accumulator
    hsp_mse_gen.set_worst_case_for_acc(MAX_HSP_BANDS); // Set worst case values for the accumulator
    hsp_mse_gen.band_packer(hsp_mse_gen.vctr1, vctr1);
    hsp_mse_gen.band_packer(hsp_mse_gen.vctr2, vctr2);
    hsp_mse_gen.sq_df_acc_vctr(hsp_mse_gen.vctr1, hsp_mse_gen.vctr2, acc_inter[0]);
    hsp_mse_gen.mse(acc_inter[0], exp_mse[0], exp_acc_of[0]); //exp_mse_of[0]
    hsp_band_packs = (hsp_mse_gen.hsp_bands + 1) / 2;
    $display("Bands: %0d, Expected MSE: %0d, Expected acc_of: %0d", hsp_mse_gen.hsp_bands, exp_mse[0], exp_acc_of[0]);
    for(int i=0; i<hsp_band_packs; i++) begin
      band_pack_valid = 1; // Enable input sample data
      band_pack_start = (i == 0); // Enable initial accumulator value on first element
      band_pack_last = (i == hsp_band_packs - 1); // Set last flag for the last element
      band_pack_a = vctr1[i]; // Use maximum value for the word
      band_pack_b = vctr2[i]; // Use zero for the second word to get maximum difference
      hsp_bands = MAX_HSP_BANDS; // Set maximum HSP bands
      vctr_ref = MAX_HSP_LIBRARY; // Set maximum reference vector
      #10; // Wait for a clock cycle
    end

    // Disable input sample data
    band_pack_valid = 0;

    #(10 * mse_pipeline); // Wait for the last MSE calculation to complete
    a_max_acc_of_valid: assert (mse_valid) else $fatal(0, "MSE valid signal is not asserted after overflow test, please check pipeline waiting cycles");
    a_max_acc_of: assert (!acc_of) else $error("Accumulator overflow flag is not set after overflow test");
    // a_max_mse_of: assert (mse_of == exp_mse_of[0]) else $error("MSE overflow flag is not set after overflow test, expected %0d, got %0d", exp_mse_of[0], mse_of);
    a_max_acc_value: assert (mse_value == exp_mse[0]) else $error("Accumulator value is not as we expected after overflow test, got %0h", mse_value);

    $display("Case 5: Send completely random values to mse module without check results...");
    for (int i =0; i<100; i++) begin
      if(!hsp_mse_complete_gen.randomize()) $fatal(0, "Failed to randomize values");
      band_pack_valid = hsp_mse_complete_gen.band_pack_valid;
      //hsp_mse_complete_gen.band_pack_start; // Enable initial accumulator value on first element
      band_pack_last = ((i-1) % 5 ==0); //hsp_mse_complete_gen.band_pack_last; // Set last flag for the last element
      band_pack_a = hsp_mse_complete_gen.band_pack_a; // Use maximum value for the word
      band_pack_b = hsp_mse_complete_gen.band_pack_b; // Use zero for the second word to get maximum difference
      if (i % 5 == 0) begin
        band_pack_start = 1;
        hsp_bands = hsp_mse_complete_gen.hsp_bands;
        vctr_ref = hsp_mse_complete_gen.vctr_ref;
      end
      #10; // Wait for a clock cycle
    end

    #20; // Wait for the last cycle to complete


    if (TEST_OVERFLOW) begin
      $display("Case 6: Reaching overflow in the accumulator, but it doesn't have to be real because it sends more data that it should...");
      overflow_sends = 'h10008; // Reset overflow sends count
      $display("This is hacked to send more than 10000 elements to the accumulator, so it should overflow");
      for(int i=0; i<overflow_sends; i++) begin
        band_pack_valid = 1; // Enable input sample data
        band_pack_start = (i == 0); // Enable initial accumulator value on first element
        band_pack_last = (i == overflow_sends - 1); // Set last flag for the last element
        band_pack_a = (i == overflow_sends -1) ? {{16'b1}, {16'b0}} : MAX_WORD; // Use maximum value for the word
        band_pack_b = 32'b0; // Use zero for the second word to get maximum difference
        hsp_bands = MAX_HSP_BANDS; // Set maximum HSP bands
        vctr_ref = MAX_HSP_LIBRARY; // Set maximum reference vector
        #10; // Wait for a clock cycle
      end

      // Disable input sample data
      band_pack_valid = 0;

      #(10 * mse_pipeline); // Wait for the last MSE calculation to complete
      a_of_acc_valid: assert (mse_valid) else $fatal(0, "MSE valid signal is not asserted after overflow test, please check pipeline waiting cycles");
      a_of_acc_of: assert (acc_of) else $error("Accumulator overflow flag is not set after overflow test");
      // a_acc_value: assert (mse_value == exp_mse[0]) else $error("Accumulator value is not as we expected after overflow test, got %0h", mse_value);

      #20; // Wait for the last cycle to complete
    end

    $finish;
  end

  always
    #5 clk = ! clk;

  task check_mse;
    a_mse_valid: assert (mse_valid) else $fatal(0, "Test %0d: MSE valid signal is not asserted when expected, check compute waiting cycles", mse_order);
    // a_mse_of: assert (mse_of == exp_mse_of[mse_order]) else $error("Test %0d: MSE overflow flag is incorrect: expected %0d, got %0d", mse_order, exp_mse_of[mse_order], mse_of);
    a_acc_of: assert (acc_of == exp_acc_of[mse_order]) else $error("Test %0d: Accumulator overflow flag is incorrect: expected %0d, got %0d", mse_order, exp_acc_of[mse_order], acc_of);
    a_mse_value: assert (mse_value == exp_mse[mse_order]) else begin
      $error("Test %0d: MSE is incorrect: expected %0h, got %0h", mse_order, exp_mse[mse_order], mse_value);
    end
    a_mse_ref: assert (mse_ref == exp_id[mse_order]) else begin
      $error("Test %0d: Reference vector is incorrect: expected %0d, got %0d", mse_order, exp_id[mse_order], mse_ref);
    end
    mse_order++;
  endtask

endmodule