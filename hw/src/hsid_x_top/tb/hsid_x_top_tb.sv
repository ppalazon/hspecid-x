`timescale 1ns / 1ps

import hsid_pkg::*;
import registers_tb_tasks::*;
import hsid_x_ctrl_reg_pkg::*;

module hsid_x_top_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than DATA_WIDTH
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,
    parameter BUFFER_WIDTH = HSID_FIFO_ADDR_WIDTH,  // Length of the buffer
    parameter TEST_MEM_MASK = 32'h0000FFFF,  // Mask to return least significant 14 bits of the address
    parameter TEST_VALUE_MODULE_LSB = 13, // Apply the mask and then modulo to get the value
    parameter TEST_VALUE_MODULE_MSB = 17 // Apply the mask and then modulo to get the value
  ) ();

  localparam K = WORD_WIDTH;
  localparam MAX_WORD = {WORD_WIDTH{1'b1}};  // Maximum value for a word

  reg clk;
  reg rst_n;
  hsid_x_reg_pkg::reg_req_t reg_req;
  hsid_x_reg_pkg::reg_rsp_t reg_rsp;
  hsid_x_obi_inf_pkg::obi_resp_t obi_rsp;
  hsid_x_obi_inf_pkg::obi_req_t obi_req;
  wire hsid_x_int_o;

  // HSP OBI memory interface
  reg random_gnt; // Random grant signal
  reg def_gnt; // Default grant signal for the OBI bus when there is no request

  // Compute expected mse values for each pixel in the library
  logic [DATA_WIDTH-1:0] captured_hsp [];
  logic [DATA_WIDTH-1:0] reference_hsp [];
  logic [DATA_WIDTH_ACC:0] acc_int [];
  logic [WORD_WIDTH-1:0] expected_mse [];
  logic expected_mse_of [];
  logic [WORD_WIDTH-1:0] da_addr; // Direct access address
  logic [WORD_WIDTH-1:0] min_mse_value_expected;
  logic [WORD_WIDTH-1:0] max_mse_value_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] min_mse_ref_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] max_mse_ref_expected;

  // HSID X Top DUT instantiation
  hsid_x_top #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .BUFFER_WIDTH(BUFFER_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .reg_req_i(reg_req),
    .reg_rsp_o(reg_rsp),
    .obi_rsp_i(obi_rsp),
    .obi_req_o(obi_req),
    .hsid_x_int_o(hsid_x_int_o)
  );

  // Register interface debug
  reg_inf_debug reg_inf_debug_inst (
    .clk    (clk),
    .reg_req(reg_req),
    .reg_rsp(reg_rsp),
    .rst_n  (rst_n)
  );

  // OBI bus
  obi_bus_debug obi_bus_debug_inst (
    .clk    (clk),
    .rst_n  (rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp)
  );

  // Connect test memory on the OBI bus
  hsp_obi_mem #(
    .DATA_WIDTH(DATA_WIDTH),
    .VALUE_MASK(TEST_MEM_MASK),
    .VALUE_MODULE_LSB(13),
    .VALUE_MODULE_MSB(17)
  ) hsp_obi_mem_inst (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp),
    .random_gnt(random_gnt),
    .def_gnt(def_gnt)
  );

  `ifdef MODEL_TECH
  bind hsid_x_top_fsm hsid_x_top_fsm_sva #(
    .HSP_BANDS_WIDTH (HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .WORD_WIDTH(WORD_WIDTH)
  ) dut_sva (.*);

  bind hsid_x_obi_mem hsid_x_obi_mem_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .MEM_ACCESS_WIDTH(MEM_ACCESS_WIDTH)
  ) hsp_obi_mem_sva_inst (.*);

  bind hsid_x_registers hsid_x_registers_sva #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_x_registers_sva_inst (.*);

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

  bind hsid_divider hsid_divider_sva #(
    .K(K),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) hsid_divider_sva_inst (.*);
  `endif

  logic [WORD_WIDTH-1:0] library_size_w;
  logic [WORD_WIDTH-1:0] hsp_bands_w;
  logic [WORD_WIDTH-1:0] captured_hsp_addr_w;
  logic [WORD_WIDTH-1:0] library_hsp_addr_w;

  int wait_cycles_before_clear;

  // Constrained randomization classes
  HsidXTopGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),  // Data width for multiplication, larger than DATA_WIDTH
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),  // Data width for accumulator, larger than DATA_WIDTH
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH), // Address width for HSP bands
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH) // Address width for HSI library
  ) hsid_x_top_gen = new();

  HsidXRegistersRandom #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH)
  ) hsid_x_ctrl_reg_random = new();

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_x_top_tb);
  end

  // Compute expected MSE values for each pixel in the library
  initial begin
    clk = 1;
    rst_n = 1;
    reg_req = hsid_x_reg_pkg::reg_req_t'(0);
    random_gnt = 0;
    def_gnt = 0;

    #3 rst_n = 0; // Reset the DUT
    #5 rst_n = 1; // Release reset

    $display("Case 1: Normal scenario with constrained random cases...");
    for (int i = 0; i < 10; i++) begin
      if(!hsid_x_top_gen.randomize()) $fatal(0, "Randomization failed");

      // Compute expected values
      compute_expected(i);

      // Initialize variables
      library_size_w = {{WORD_WIDTH-HSP_LIBRARY_WIDTH{1'b0}},hsid_x_top_gen.library_size};
      hsp_bands_w = {{WORD_WIDTH-HSP_BANDS_WIDTH{1'b0}}, hsid_x_top_gen.hsp_bands};
      captured_hsp_addr_w = hsid_x_top_gen.captured_pixel_addr_w;
      library_hsp_addr_w = hsid_x_top_gen.library_pixel_addr_w;

      // Check status register
      if (i == 0) begin
        assert_read_reg(HSID_X_CTRL_STATUS, STATUS_IDLE);
      end else begin
        assert_read_reg(HSID_X_CTRL_STATUS, STATUS_IDLE | STATUS_DONE);
      end

      // Initialize registers
      write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, hsp_bands_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, library_size_w);

      // Check initialized values
      assert_read_reg(HSID_X_CTRL_LIBRARY_SIZE, library_size_w);
      assert_read_reg(HSID_X_CTRL_PIXEL_BANDS, hsp_bands_w);
      assert_read_reg(HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_hsp_addr_w);
      assert_read_reg(HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_hsp_addr_w);

      // Start the processing
      write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_START);

      // Wait for the processing to complete, but add a delay to avoid problems with the clock
      wait (hsid_x_int_o == 1'b1);
      #8;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE);
      #10;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE | STATUS_IDLE);

      // // Check the MSE results
      assert_read_reg(HSID_X_CTRL_MSE_MIN_REF, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, min_mse_ref_expected });
      assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE, min_mse_value_expected);
      assert_read_reg(HSID_X_CTRL_MSE_MAX_REF, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, max_mse_ref_expected });
      assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE, max_mse_value_expected);

      #20;

    end

    $display("Case 2: Error scenario with random values...");
    for (int i = 0; i < 3; i++) begin
      if(!hsid_x_top_gen.randomize()) $fatal(0, "Randomization failed");
      // Initialize variables
      library_size_w = (i[0] == 1'b0) ? '0 : {{WORD_WIDTH-HSP_LIBRARY_WIDTH{1'b0}},hsid_x_top_gen.library_size};
      hsp_bands_w = (i[1] == 1'b0) ? '0 : {{WORD_WIDTH-HSP_BANDS_WIDTH{1'b0}}, hsid_x_top_gen.hsp_bands};
      captured_hsp_addr_w = hsid_x_top_gen.captured_pixel_addr_w;
      library_hsp_addr_w = hsid_x_top_gen.library_pixel_addr_w;

      $display("Error Test %0d: Captured Pixel Address: 0x%0h, Library Address: 0x%0h, HSP Bands: %0d, Library size: %0d", i,
        captured_hsp_addr_w, library_hsp_addr_w, hsp_bands_w, library_size_w);

      // Initialize registers
      write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, hsp_bands_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, library_size_w);

      // Start the processing
      write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_START);

      // Wait for the processing to complete, but add a delay to avoid problems with the clock
      wait (hsid_x_int_o == 1'b1);
      #8;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_ERROR);
      #10;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_ERROR | STATUS_IDLE);

      // // Check the MSE results
      assert_read_reg(HSID_X_CTRL_MSE_MIN_REF, '0);
      assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE, MAX_WORD);
      assert_read_reg(HSID_X_CTRL_MSE_MAX_REF, '0);
      assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE, '0);
    end

    $display("Case 3: Clear at different stages...");
    for (int i = 0; i < 10; i++) begin
      if(!hsid_x_top_gen.randomize()) $fatal(0, "Randomization failed");

      // Perform some operations in order to have old mse computations
      library_size_w = {{WORD_WIDTH-HSP_LIBRARY_WIDTH{1'b0}},hsid_x_top_gen.library_size};
      hsp_bands_w = {{WORD_WIDTH-HSP_BANDS_WIDTH{1'b0}}, hsid_x_top_gen.hsp_bands};
      captured_hsp_addr_w = hsid_x_top_gen.captured_pixel_addr_w;
      library_hsp_addr_w = hsid_x_top_gen.library_pixel_addr_w;

      $display("Clear Test %0d: Captured Pixel Address: 0x%0h, Library Address: 0x%0h, HSP Bands: %0d, Library size: %0d", i,
        captured_hsp_addr_w, library_hsp_addr_w, hsp_bands_w, library_size_w);

      write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, hsp_bands_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, library_size_w);

      // Start the processing
      write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_START);

      wait (hsid_x_int_o == 1'b1);
      #8;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE);

      #10;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE | STATUS_IDLE);

      // Start again to perform the clear operation

      // Start the processing
      write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_START);

      case (i)
        0: wait_cycles_before_clear = 2; // Clear on config
        1: wait_cycles_before_clear = hsp_bands_w / 2; // Clear on reading captured pixel
        2: wait_cycles_before_clear = (hsp_bands_w * library_size_w) / 2; // Random wait cycles before clearing
        default: wait_cycles_before_clear = $urandom_range(0, (hsp_bands_w * library_size_w) / 2);
      endcase

      $display("Waiting %0d cycles before clearing...", wait_cycles_before_clear);
      #(wait_cycles_before_clear * 10); // Wait for the specified cycles

      // Send clear command
      write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_CLEAR);

      // Wait for the processing to complete, but add a delay to avoid problems with the clock
      wait (hsid_x_int_o == 1'b1);
      #8;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_CANCELLED);

      #10;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_CANCELLED | STATUS_IDLE);

      // // Check the MSE results
      assert_read_reg(HSID_X_CTRL_MSE_MIN_REF, '0);
      assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE, MAX_WORD);
      assert_read_reg(HSID_X_CTRL_MSE_MAX_REF, '0);
      assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE, '0);

    end

    // This case is only for ModelSim, because it provokes a fatal error in Vivado
    `ifdef MODEL_TECH
    $display("Case 4: Modify registers during processing with random values...");
    for (int i = 0; i < 10; i++) begin
      if(!hsid_x_top_gen.randomize()) $fatal(0, "Randomization failed");

      // Compute expected values
      compute_expected(i);

      // Initialize variables
      library_size_w = {{WORD_WIDTH-HSP_LIBRARY_WIDTH{1'b0}},hsid_x_top_gen.library_size};
      hsp_bands_w = {{WORD_WIDTH-HSP_BANDS_WIDTH{1'b0}}, hsid_x_top_gen.hsp_bands};
      captured_hsp_addr_w = hsid_x_top_gen.captured_pixel_addr_w;
      library_hsp_addr_w = hsid_x_top_gen.library_pixel_addr_w;

      // Check status register
      // assert_read_reg(HSID_X_CTRL_STATUS, STATUS_IDLE);

      // Initialize registers
      write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_hsp_addr_w);
      write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, hsp_bands_w);
      write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, library_size_w);

      // Check initialized values
      assert_read_reg(HSID_X_CTRL_LIBRARY_SIZE, library_size_w);
      assert_read_reg(HSID_X_CTRL_PIXEL_BANDS, hsp_bands_w);
      assert_read_reg(HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_hsp_addr_w);
      assert_read_reg(HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_hsp_addr_w);

      // Start the processing
      write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_START);

      #10; // Wait a cycle to allow the FSMs getting configured values

      wait_and_reg: fork

        begin
          wait (hsid_x_int_o == 1'b1);
        end

        begin
          forever begin
            @(posedge clk); // sync to DUT clock, not # delays
            #8;
            if(!hsid_x_ctrl_reg_random.randomize()) $fatal(0, "Randomization failed");

            // Modify registers with random values
            write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, hsid_x_ctrl_reg_random.captured_pixel_addr);
            write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, hsid_x_ctrl_reg_random.library_pixel_addr);
            write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, {{(WORD_WIDTH-HSP_BANDS_WIDTH){1'b0}}, hsid_x_ctrl_reg_random.hsp_bands});
            write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, hsid_x_ctrl_reg_random.hsp_library_size});

          end
        end
      join_any

      disable wait_and_reg;
      #8;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE);
      #10;
      assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE | STATUS_IDLE);

// // Check the MSE results
      assert_read_reg(HSID_X_CTRL_MSE_MIN_REF, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, min_mse_ref_expected });
      assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE, min_mse_value_expected);
      assert_read_reg(HSID_X_CTRL_MSE_MAX_REF, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, max_mse_ref_expected });
      assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE, max_mse_value_expected);

      #20;

    end
    `endif


    $finish;

  end

  always
    #5 clk = ! clk;

  initial begin
    #500000; $fatal(0, "Testbench timeout"); // Timeout if the test does not finish
  end

  task assert_read_reg(input hsid_x_ctrl_id_e ctrl_id, logic [WORD_WIDTH-1:0] expected);
    read_reg(reg_req, ctrl_id);
    assert_value(reg_rsp.rdata, expected, $sformatf("BUS read addr: 0x%0h (%s)", addr_reg(ctrl_id), ctrl_id.name()));
  endtask

  task expected_pixel_mem(input logic [31:0] addr, input logic [HSP_BANDS_WIDTH-1:0] bands, output logic [DATA_WIDTH-1:0] hsp []);
    logic [DATA_WIDTH-1:0] msb_pixel_value;
    logic [DATA_WIDTH-1:0] lsb_pixel_value;
    hsp = new[bands];
    for (int i = 0; i < bands; i=i+2) begin
      // msb_pixel_value = addr[WORD_WIDTH-1:DATA_WIDTH] & TEST_MEM_MASK;
      msb_pixel_value = (addr[DATA_WIDTH-1:0] & TEST_MEM_MASK) % TEST_VALUE_MODULE_MSB;
      lsb_pixel_value = (addr[DATA_WIDTH-1:0] & TEST_MEM_MASK) % TEST_VALUE_MODULE_LSB;
      // $display("Reading pixel data from address: 0x%0h: 0x%0h", addr, masked_data);
      hsp[i] = msb_pixel_value;
      hsp[i+1] = lsb_pixel_value;
      addr = addr + 4;
    end
  endtask

  task compute_expected(input int test_id);
    // Get expected captured pixel
    expected_pixel_mem(hsid_x_top_gen.captured_pixel_addr_w, hsid_x_top_gen.hsp_bands, captured_hsp);
    $display("Test %0d: Captured Pixel Address: 0x%0h, Library Address: 0x%0h, HSP Bands: %0d, Library size: %0d", test_id,
      hsid_x_top_gen.captured_pixel_addr_w, hsid_x_top_gen.library_pixel_addr_w, hsid_x_top_gen.hsp_bands, hsid_x_top_gen.library_size);

    //hsid_x_top_gen.display_hsp("Captured HSP", captured_hsp);

    // Get expected mse values for the library pixels
    expected_mse = new[hsid_x_top_gen.library_size];
    expected_mse_of = new[hsid_x_top_gen.library_size];
    for (int j = 0; j < hsid_x_top_gen.library_size; j++) begin
      da_addr = hsid_x_top_gen.library_pixel_addr_w + (j * 4 * hsid_x_top_gen.hsp_bands_packs); // Address for each band
      expected_pixel_mem(da_addr, hsid_x_top_gen.hsp_bands, reference_hsp);
      hsid_x_top_gen.sq_df_acc_vctr(captured_hsp, reference_hsp, acc_int);
      hsid_x_top_gen.mse(acc_int, expected_mse[j], expected_mse_of[j]);
      // hsid_x_top_gen.display_hsp("Reference HSP", reference_hsp);
      // $display("Accumulator: %p, MSE: %0d, Overflow: %0b", acc_int, expected_mse[j], expected_mse_of[j]);
      // $display("Library Pixel %0d: %p, MSE: %0d", j, reference_hsp, expected_mse[j]);
    end
    // $display(" - Vector sizes: captured %0d, reference %0d, accumulator %0d", captured_hsp.size(), reference_hsp.size(), acc_int.size());
    // $display(" - Expected MSE values: %p", expected_mse);

    // Compute expected min and max MSE values and references
    hsid_x_top_gen.min_max_mse(expected_mse,
      min_mse_value_expected, max_mse_value_expected,
      min_mse_ref_expected, max_mse_ref_expected);

    $display(" - Expected min MSE: %0d, ref: %0d", min_mse_value_expected, min_mse_ref_expected);
    $display(" - Expected max MSE: %0d, ref: %0d", max_mse_value_expected, max_mse_ref_expected);
  endtask

endmodule