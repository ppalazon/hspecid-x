`timescale 1ns / 1ps

import hsid_pkg::*;
import ctrl_reg_tb_tasks::*;
import hsid_x_ctrl_reg_pkg::*;

module hsid_x_top_tb #(
    parameter WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter DATA_WIDTH_MUL = HSID_DATA_WIDTH_MUL,  // Data width for multiplication, larger than DATA_WIDTH
    parameter DATA_WIDTH_ACC = HSID_DATA_WIDTH_ACC,  // Data width for accumulator, larger than DATA_WIDTH
    parameter DATA_WIDTH = HSID_DATA_WIDTH,  // 16 bits by default
    parameter HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH,
    parameter HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,
    parameter BUFFER_WIDTH = HSID_BUFFER_WIDTH,  // Length of the buffer
    parameter TEST_BANDS = HSID_TEST_BANDS, // Number of HSI bands to test
    parameter TEST_ELEMENTS = TEST_BANDS / 2, // Number of HSI bands to test
    parameter TEST_LIBRARY_SIZE = HSID_TEST_LIBRARY_SIZE, // Size of the HSI library to test
    parameter TEST_MEM_RND_GNT = 1,
    parameter TEST_MEM_RND_VALUE = 0,
    parameter TEST_MEM_MASK = 32'h00003FFF,  // Mask to return least significant 14 bits of the address
    parameter TEST_CAPTURED_PIXEL_ADDR = 32'h00000004, // Address for captured pixel data
    parameter TEST_LIBRARY_PIXEL_ADDR = 32'h00010004 - (3 * TEST_ELEMENTS * 4)  // Address for library pixel data, 4 pixels is the same as captured pixel data
  ) ();

  reg clk;
  reg rst_n;
  hsid_x_reg_pkg::reg_req_t reg_req;
  hsid_x_reg_pkg::reg_rsp_t reg_rsp;
  hsid_x_obi_inf_pkg::obi_resp_t obi_rsp;
  hsid_x_obi_inf_pkg::obi_req_t obi_req;
  wire hsid_x_int_o;

  // Compute expected mse values for each pixel in the library
  logic [DATA_WIDTH-1:0] captured_pixel [TEST_BANDS];
  logic [DATA_WIDTH-1:0] reference_pixel [TEST_BANDS];
  logic [WORD_WIDTH-1:0] expected_mse [TEST_LIBRARY_SIZE];
  logic [WORD_WIDTH-1:0] da_addr; // Direct access address
  logic [WORD_WIDTH-1:0] min_mse_value_expected;
  logic [WORD_WIDTH-1:0] max_mse_value_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] min_mse_ref_expected;
  logic [HSP_LIBRARY_WIDTH-1:0] max_mse_ref_expected;

  hsid_x_top #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH),
    .BUFFER_WIDTH(BUFFER_WIDTH)
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
  reg_inf_debug u_reg_inf_debug (
    .clk    (clk),
    .reg_req(reg_req),
    .reg_rsp(reg_rsp),
    .rst_n  (rst_n)
  );

  // OBI bus
  obi_bus_debug u_obi_bus_debug (
    .clk    (clk),
    .rst_n  (rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp)
  );

  // Connect test memory on the OBI bus
  pixel_obi_mem #(
    .DATA_WIDTH(DATA_WIDTH),
    .RANDOM_GNT(TEST_MEM_RND_GNT),
    .RANDOM_VALUE(TEST_MEM_RND_VALUE),
    .VALUE_MASK(TEST_MEM_MASK)
  ) u_pixel_obi_mem (
    .clk(clk),
    .rst_n(rst_n),
    .obi_req(obi_req),
    .obi_rsp(obi_rsp)
  );

  const int STATUS_START = 32'b000001;
  const int STATUS_CLEAR = 32'b010000;
  const int STATUS_IDLE = 32'b000010;
  const int STATUS_DONE = 32'b001000;

  logic [WORD_WIDTH-1:0] library_size_w;
  logic [WORD_WIDTH-1:0] pixel_bands_w;
  logic [WORD_WIDTH-1:0] captured_pixel_addr_w;
  logic [WORD_WIDTH-1:0] library_pixel_addr_w;

  HsidMainGen #(
    .WORD_WIDTH(WORD_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DATA_WIDTH_MUL(DATA_WIDTH_MUL),  // Data width for multiplication, larger than DATA_WIDTH
    .DATA_WIDTH_ACC(DATA_WIDTH_ACC),  // Data width for accumulator, larger than DATA_WIDTH
    .TEST_BANDS(TEST_BANDS),
    .TEST_LIBRARY_SIZE(TEST_LIBRARY_SIZE)
  ) hsid_main_gen = new();

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_x_top_tb);
  end

  // Compute expected MSE values for each pixel in the library
  initial begin
    // Get captured pixel data from the memory
    read_pixel_mem(TEST_CAPTURED_PIXEL_ADDR, captured_pixel);
    $display("Captured Pixel Data:    %p", captured_pixel);
    // Get reference pixel data from the memory and compute expected MSE
    for (int j = 0; j < TEST_LIBRARY_SIZE; j++) begin
      da_addr = TEST_LIBRARY_PIXEL_ADDR + (j * 4 * TEST_ELEMENTS); // Address for each band
      read_pixel_mem(da_addr, reference_pixel);
      hsid_main_gen.mse(captured_pixel, reference_pixel, expected_mse[j]);
      $display("Library Pixel %0d: %p, MSE: %0d", j, reference_pixel, expected_mse[j]);
    end
    // Compute expected min and max MSE values and references
    hsid_main_gen.min_max_mse(expected_mse,
      min_mse_value_expected, max_mse_value_expected,
      min_mse_ref_expected, max_mse_ref_expected);

    $display("Expected min MSE: %0d, ref: %0d", min_mse_value_expected, min_mse_ref_expected);
    $display("Expected max MSE: %0d, ref: %0d", max_mse_value_expected, max_mse_ref_expected);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    reg_req = hsid_x_reg_pkg::reg_req_t'(0);

    #3 rst_n = 0; // Reset the DUT
    #5 rst_n = 1; // Release reset

    // Initialize variables
    library_size_w = TEST_LIBRARY_SIZE;
    pixel_bands_w = TEST_BANDS;
    captured_pixel_addr_w = TEST_CAPTURED_PIXEL_ADDR;
    library_pixel_addr_w = TEST_LIBRARY_PIXEL_ADDR;

    // Check status register
    assert_read_reg(HSID_X_CTRL_STATUS, STATUS_IDLE);

    // Initialize registers
    write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, library_size_w);
    write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, pixel_bands_w);
    write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_pixel_addr_w);
    write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_pixel_addr_w);

    // Check initialized values
    assert_read_reg(HSID_X_CTRL_LIBRARY_SIZE, library_size_w);
    assert_read_reg(HSID_X_CTRL_PIXEL_BANDS, pixel_bands_w);
    assert_read_reg(HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_pixel_addr_w);
    assert_read_reg(HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_pixel_addr_w);

    // Start the processing
    write_reg(reg_req, HSID_X_CTRL_STATUS, STATUS_START);

    // Wait for the processing to complete
    wait (hsid_x_int_o == 1'b1);
    #10;
    assert_read_reg(HSID_X_CTRL_STATUS, STATUS_DONE);
    #10;
    assert_read_reg(HSID_X_CTRL_STATUS, STATUS_IDLE);

    // // Check the MSE results
    assert_read_reg(HSID_X_CTRL_MSE_MIN_REF, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, min_mse_ref_expected });
    assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE, min_mse_value_expected);
    assert_read_reg(HSID_X_CTRL_MSE_MAX_REF, {{(WORD_WIDTH-HSP_LIBRARY_WIDTH){1'b0}}, max_mse_ref_expected });
    assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE, max_mse_value_expected);

    #20;

    $finish;

  end

  always
    #5 clk = ! clk;

  initial begin
    #2000; $finish; // Timeout if the test does not finish
  end

  task assert_read_reg(input hsid_x_ctrl_id_e ctrl_id, logic [WORD_WIDTH-1:0] expected);
    read_reg(reg_req, ctrl_id);
    assert_value(reg_rsp.rdata, expected, $sformatf("BUS read addr: 0x%0h (%s)", addr_reg(ctrl_id), ctrl_id.name()));
  endtask

  task read_pixel_mem(input logic [31:0] addr, output logic [DATA_WIDTH-1:0] pixel [TEST_BANDS]);
    logic [DATA_WIDTH-1:0] masked_data; // Data read from the memory
    for (int i = 0; i < TEST_BANDS; i=i+2) begin
      masked_data = addr[DATA_WIDTH-1:0] & TEST_MEM_MASK;
      // $display("Reading pixel data from address: 0x%0h: 0x%0h", addr, masked_data);
      pixel[i] = masked_data;
      pixel[i+1] = masked_data;
      addr = addr + 4;
    end
  endtask

endmodule