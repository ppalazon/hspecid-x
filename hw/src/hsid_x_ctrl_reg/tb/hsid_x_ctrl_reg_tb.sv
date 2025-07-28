`timescale 1ns / 1ps

import hsid_pkg::*;
import hsid_x_ctrl_reg_pkg::*;
import ctrl_reg_tb_tasks::*;

`include "register_interface/typedef.svh"

module hsid_x_ctrl_reg_tb #(
    parameter int WORD_WIDTH = HSID_WORD_WIDTH,  // Width of the word in bits
    parameter int HSP_BANDS_WIDTH = HSID_HSP_BANDS_WIDTH,  // Address width for HSP bands
    parameter int HSP_LIBRARY_WIDTH = HSID_HSP_LIBRARY_WIDTH  // Address width for HSI library size
  );

  reg clk;
  reg rst_n;
  wire start;
  wire clear;
  reg idle;
  reg done;
  reg error;
  reg ready;
  wire [HSP_LIBRARY_WIDTH-1:0] library_size;
  wire [HSP_BANDS_WIDTH-1:0] pixel_bands;
  wire [WORD_WIDTH-1:0] captured_pixel_addr;
  wire [WORD_WIDTH-1:0] library_pixel_addr;
  reg [HSP_LIBRARY_WIDTH-1:0] mse_min_ref;
  reg [WORD_WIDTH-1:0] mse_min_value;
  reg [HSP_LIBRARY_WIDTH-1:0] mse_max_ref;
  reg [WORD_WIDTH-1:0] mse_max_value;

  logic [WORD_WIDTH-1:0] data_in;
  logic [WORD_WIDTH-1:0] data_out;

  // Create word size variable for comparisons
  logic [WORD_WIDTH-1:0] library_size_w;
  logic [WORD_WIDTH-1:0] pixel_bands_w;
  logic [WORD_WIDTH-1:0] start_w;
  logic [WORD_WIDTH-1:0] clear_w;
  logic [WORD_WIDTH-1:0] mse_max_ref_w;
  logic [WORD_WIDTH-1:0] mse_min_ref_w;

  assign library_size_w = {{(32-HSP_LIBRARY_WIDTH){1'b0}}, library_size};
  assign pixel_bands_w = {{(32-HSP_BANDS_WIDTH){1'b0}}, pixel_bands};
  assign start_w = {31'b0, start};
  assign clear_w = {31'b0, clear};
  assign mse_max_ref_w = {{(32-HSP_LIBRARY_WIDTH){1'b0}}, mse_max_ref};
  assign mse_min_ref_w = {{(32-HSP_LIBRARY_WIDTH){1'b0}}, mse_min_ref};


  // REG_BUS #(.ADDR_WIDTH(32), .DATA_WIDTH(32)) regbus_slave(clk);
  hsid_x_reg_pkg::reg_req_t reg_req;
  hsid_x_reg_pkg::reg_rsp_t reg_rsp;

  hsid_x_ctrl_reg #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSP_BANDS_WIDTH(HSP_BANDS_WIDTH),
    .HSP_LIBRARY_WIDTH(HSP_LIBRARY_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    // .regbus_slave(regbus_slave.in),
    .reg_req(reg_req),
    .reg_rsp(reg_rsp),
    .start(start),
    .clear(clear),
    .idle(idle),
    .ready(ready),
    .done(done),
    .error(error),
    .library_size(library_size),
    .pixel_bands(pixel_bands),
    .captured_pixel_addr(captured_pixel_addr),
    .library_pixel_addr(library_pixel_addr),
    .mse_min_ref(mse_min_ref),
    .mse_min_value(mse_min_value),
    .mse_max_ref(mse_max_ref),
    .mse_max_value(mse_max_value)
  );

  // Register interface debug module
  reg_inf_debug reg_inf_debug_inst (
    .clk(clk),
    .rst_n(rst_n),
    .reg_req(reg_req),
    .reg_rsp(reg_rsp)
  );

  // Waveform generation for debugging
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, hsid_x_ctrl_reg_tb);
  end

  initial begin
    clk = 1;
    rst_n = 1;
    idle = 0;
    ready = 0;
    done = 0;
    error = 0;
    mse_min_ref = 0;
    mse_min_value = 0;
    mse_max_ref = 0;
    mse_max_value = 0;

    // Initialize the register interface request
    // regbus_slave.valid = 0;
    // regbus_slave.write = 0;
    // regbus_slave.addr = 0;
    // regbus_slave.wdata = 0;
    reg_req = '0; // Initialize register request

    #3 rst_n = 0;  // Reset the DUT
    #5 rst_n = 1; // Release reset

    $display("Case 1: Write input arguments");
    // Writing library size
    data_in = 10;
    // write_reg(HSID_X_CTRL_LIBRARY_SIZE_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_LIBRARY_SIZE], data_in);
    write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, data_in);
    assert_value(library_size_w, 10, "Library size");

    data_in = 32'hFFFFFFFF;
    write_reg(reg_req, HSID_X_CTRL_LIBRARY_SIZE, data_in);
    assert_value(library_size_w, 2**HSP_LIBRARY_WIDTH - 1, "Library size limited to 13 bits");

    // Writing pixel bands
    data_in = 5;
    write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, data_in);
    assert_value(pixel_bands_w, 5, "Pixel bands after write");

    data_in = 32'hFFFFFFFF;
    write_reg(reg_req, HSID_X_CTRL_PIXEL_BANDS, data_in);
    assert_value(pixel_bands_w, 2 ** HSP_BANDS_WIDTH - 1, "Pixel bands limited to 9 bits");

    // Writing captured pixel addr
    data_in = 32'h12345678;
    write_reg(reg_req, HSID_X_CTRL_CAPTURED_PIXEL_ADDR, data_in);
    assert_value(captured_pixel_addr, 32'h12345678, "Captured pixel address after write");

    // Writing library pixel addr
    data_in = 32'h87654321;
    write_reg(reg_req, HSID_X_CTRL_LIBRARY_PIXEL_ADDR, data_in);
    assert_value(library_pixel_addr, 32'h87654321, "Library pixel address after write");

    $display("Case 2: Read input arguments");
    assert_read_reg(HSID_X_CTRL_LIBRARY_SIZE, library_size_w);
    assert_read_reg(HSID_X_CTRL_PIXEL_BANDS, pixel_bands_w);
    assert_read_reg(HSID_X_CTRL_CAPTURED_PIXEL_ADDR, captured_pixel_addr);
    assert_read_reg(HSID_X_CTRL_LIBRARY_PIXEL_ADDR, library_pixel_addr);

    $display("Case 3: Status register - start and clear");
    data_in = 32'b000001; // Start (bit 0)
    write_reg(reg_req, HSID_X_CTRL_STATUS, data_in);
    assert_value(start_w, 1, "Start signal");
    assert_value(clear_w, 0, "Clear signal");

    #10;
    assert_value(start_w, 0, "Start signal after one clock cycle");
    assert_value(clear_w, 0, "Clear signal after one clock cycle");

    data_in = 32'b010000; // Clear (bit 4)
    write_reg(reg_req, HSID_X_CTRL_STATUS, data_in);
    assert_value(start_w, 0, "Start signal");
    assert_value(clear_w, 1, "Clear signal");

    #10;
    assert_value(start_w, 0, "Start signal after one clock cycle");
    assert_value(clear_w, 0, "Clear signal after one clock cycle");

    data_in = 32'b010001; // Start & Clear (bit 0 y 4)
    write_reg(reg_req, HSID_X_CTRL_STATUS, data_in);
    assert_value(start_w, 1, "Start signal");
    assert_value(clear_w, 1, "Clear signal");

    #10;
    assert_value(start_w, 0, "Start signal after one clock cycle");
    assert_value(clear_w, 0, "Clear signal after one clock cycle");

    data_in = $urandom(); // Random data
    write_reg(reg_req, HSID_X_CTRL_STATUS, data_in);
    assert_value(start_w, {31'b0,data_in[0]}, "Start signal after random write");
    assert_value(clear_w, {31'b0,data_in[4]}, "Clear signal after random write");

    #10;

    $display("Case 4: Hardware wire status and reading bus");
    idle = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b000010);
    ready = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b000110);
    done = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b001110);
    error = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b101110);
    idle = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b101100);
    ready = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b101000);
    done = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b100000);
    error = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS, 32'b000000);

    $display("Case 5: Reading outputs");
    mse_max_ref = $urandom() % (2**HSP_LIBRARY_WIDTH);
    mse_max_value = $urandom();
    mse_min_ref = $urandom() % (2**HSP_LIBRARY_WIDTH);
    mse_min_value = $urandom();
    #10;

    assert_read_reg(HSID_X_CTRL_MSE_MAX_REF, mse_max_ref_w);
    assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE, mse_max_value);
    assert_read_reg(HSID_X_CTRL_MSE_MIN_REF, mse_min_ref_w);
    assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE, mse_min_value);

    $finish; // End simulation

  end

  always
    #5 clk = ! clk;

  task assert_read_reg(input hsid_x_ctrl_id_e ctrl_id, logic [WORD_WIDTH-1:0] expected);
    read_reg(reg_req, ctrl_id);
    assert_value(reg_rsp.rdata, expected, $sformatf("BUS read addr: 0x%0h (%s)", addr_reg(ctrl_id), ctrl_id.name()));
  endtask

endmodule