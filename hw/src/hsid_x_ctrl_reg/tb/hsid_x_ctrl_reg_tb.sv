`timescale 1ns / 1ps

import hsid_pkg::*;
import hsid_x_ctrl_reg_pkg::*;

`include "register_interface/typedef.svh"

module hsid_x_ctrl_reg_tb;

  localparam WORD_WIDTH = HSID_WORD_WIDTH;
  localparam HSI_BANDS = HSID_MAX_HSP_BANDS - 1;
  localparam HSI_LIBRARY_SIZE = HSID_MAX_HSP_LIBRARY - 1;
  localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS);
  localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE);

  reg clk;
  reg rst_n;
  wire start;
  wire clear;
  reg idle;
  reg done;
  reg error;
  reg ready;
  wire [HSI_LIBRARY_SIZE_ADDR-1:0] library_size;
  wire [HSI_BANDS_ADDR-1:0] pixel_bands;
  wire [WORD_WIDTH-1:0] captured_pixel_addr;
  wire [WORD_WIDTH-1:0] library_pixel_addr;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref;
  reg [WORD_WIDTH-1:0] mse_min_value;
  reg [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref;
  reg [WORD_WIDTH-1:0] mse_max_value;

  logic [31:0] data_in;
  logic [31:0] data_out;

  // Create word size variable for comparisons
  logic [31:0] library_size_w;
  logic [31:0] pixel_bands_w;
  logic [31:0] start_w;
  logic [31:0] clear_w;
  logic [31:0] mse_max_ref_w;
  logic [31:0] mse_min_ref_w;

  assign library_size_w = {{(32-HSI_LIBRARY_SIZE_ADDR){1'b0}}, library_size};
  assign pixel_bands_w = {{(32-HSI_BANDS_ADDR){1'b0}}, pixel_bands};
  assign start_w = {31'b0, start};
  assign clear_w = {31'b0, clear};
  assign mse_max_ref_w = {{(32-HSI_LIBRARY_SIZE_ADDR){1'b0}}, mse_max_ref};
  assign mse_min_ref_w = {{(32-HSI_LIBRARY_SIZE_ADDR){1'b0}}, mse_min_ref};


  // REG_BUS #(.ADDR_WIDTH(32), .DATA_WIDTH(32)) regbus_slave(clk);
  hsid_x_reg_pkg::reg_req_t reg_req;
  hsid_x_reg_pkg::reg_rsp_t reg_rsp;

  hsid_x_ctrl_reg #(
    .WORD_WIDTH(WORD_WIDTH),
    .HSI_BANDS(HSI_BANDS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
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
    write_reg(HSID_X_CTRL_LIBRARY_SIZE_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_LIBRARY_SIZE], data_in);
    assert_value(library_size_w, 10, "Library size");

    data_in = 32'hFFFFFFFF;
    write_reg(HSID_X_CTRL_LIBRARY_SIZE_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_LIBRARY_SIZE], data_in);
    assert_value(library_size_w, HSI_LIBRARY_SIZE, "Library size limited to 13 bits");

    // Writing pixel bands
    data_in = 5;
    write_reg(HSID_X_CTRL_PIXEL_BANDS_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_PIXEL_BANDS], data_in);
    assert_value(pixel_bands_w, 5, "Pixel bands after write");

    data_in = 32'hFFFFFFFF;
    write_reg(HSID_X_CTRL_PIXEL_BANDS_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_PIXEL_BANDS], data_in);
    assert_value(pixel_bands_w, HSI_BANDS, "Pixel bands limited to 9 bits");

    // Writing captured pixel addr
    data_in = 32'h12345678;
    write_reg(HSID_X_CTRL_CAPTURED_PIXEL_ADDR_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_CAPTURED_PIXEL_ADDR], data_in);
    assert_value(captured_pixel_addr, 32'h12345678, "Captured pixel address after write");

    // Writing library pixel addr
    data_in = 32'h87654321;
    write_reg(HSID_X_CTRL_LIBRARY_PIXEL_ADDR_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_LIBRARY_PIXEL_ADDR], data_in);
    assert_value(library_pixel_addr, 32'h87654321, "Library pixel address after write");

    $display("Case 2: Read input arguments");
    assert_read_reg(HSID_X_CTRL_LIBRARY_SIZE_OFFSET, library_size_w);
    assert_read_reg(HSID_X_CTRL_PIXEL_BANDS_OFFSET, pixel_bands_w);
    assert_read_reg(HSID_X_CTRL_CAPTURED_PIXEL_ADDR_OFFSET, captured_pixel_addr);
    assert_read_reg(HSID_X_CTRL_LIBRARY_PIXEL_ADDR_OFFSET, library_pixel_addr);


    $display("Case 3: Status register - start and clear");
    data_in = 32'b000001; // Start (bit 0)
    write_reg(HSID_X_CTRL_STATUS_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_STATUS], data_in);
    assert_value(start_w, 1, "Start signal");
    assert_value(clear_w, 0, "Clear signal");

    #10;
    assert_value(start_w, 0, "Start signal after one clock cycle");
    assert_value(clear_w, 0, "Clear signal after one clock cycle");

    data_in = 32'b010000; // Clear (bit 4)
    write_reg(HSID_X_CTRL_STATUS_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_STATUS], data_in);
    assert_value(start_w, 0, "Start signal");
    assert_value(clear_w, 1, "Clear signal");

    #10;
    assert_value(start_w, 0, "Start signal after one clock cycle");
    assert_value(clear_w, 0, "Clear signal after one clock cycle");

    data_in = 32'b010001; // Start & Clear (bit 0 y 4)
    write_reg(HSID_X_CTRL_STATUS_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_STATUS], data_in);
    assert_value(start_w, 1, "Start signal");
    assert_value(clear_w, 1, "Clear signal");

    #10;
    assert_value(start_w, 0, "Start signal after one clock cycle");
    assert_value(clear_w, 0, "Clear signal after one clock cycle");

    data_in = $urandom(); // Random data
    write_reg(HSID_X_CTRL_STATUS_OFFSET, HSID_X_CTRL_PERMIT[HSID_X_CTRL_STATUS], data_in);
    assert_value(start_w, {31'b0,data_in[0]}, "Start signal after random write");
    assert_value(clear_w, {31'b0,data_in[4]}, "Clear signal after random write");

    #10;

    $display("Case 4: Hardware wire status and reading bus");
    idle = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b000010);
    ready = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b000110);
    done = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b001110);
    error = 1; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b101110);
    idle = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b101100);
    ready = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b101000);
    done = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b100000);
    error = 0; #10;
    assert_read_reg(HSID_X_CTRL_STATUS_OFFSET, 32'b000000);

    $display("Case 5: Reading outputs");
    mse_max_ref = $urandom() % HSI_LIBRARY_SIZE;
    mse_max_value = $urandom();
    mse_min_ref = $urandom() % HSI_LIBRARY_SIZE;
    mse_min_value = $urandom();
    #10;

    assert_read_reg(HSID_X_CTRL_MSE_MAX_REF_OFFSET, mse_max_ref_w);
    assert_read_reg(HSID_X_CTRL_MSE_MAX_VALUE_OFFSET, mse_max_value);
    assert_read_reg(HSID_X_CTRL_MSE_MIN_REF_OFFSET, mse_min_ref_w);
    assert_read_reg(HSID_X_CTRL_MSE_MIN_VALUE_OFFSET, mse_min_value);




    $finish; // End simulation

  end

  always
    #5 clk = ! clk;

  task write_reg(input logic [BlockAw-1:0] addr, input logic [3:0] wstrb, input logic [31:0] data);
    begin
      reg_req.addr = {{(WORD_WIDTH-BlockAw){1'b0}}, addr};
      reg_req.wdata = data;
      reg_req.wstrb = wstrb; // Write operation
      reg_req.write = 1;
      reg_req.valid = 1; // Indicate valid request
      #10;
      while (!reg_rsp.ready) begin
        #1; // Wait for the register interface to be ready
      end
      reg_req.write = 0; // Clear write signal
      reg_req.valid = 0; // Clear valid signal
    end
  endtask

  task assert_value(input logic [31:0] actual, input logic [31:0] expected, string message);
    if (expected !== actual) begin
      $error("ERROR: %s: expected 0x%0h, got 0x%0h", message, expected, actual);
    end else begin
      $display("PASS: %s passed: got %0d (0x%h)", message, actual, actual);
    end
  endtask

  task assert_read_reg(input logic [BlockAw-1:0] addr, input logic [31:0] expected);
    begin
      reg_req.addr = {{(WORD_WIDTH-BlockAw){1'b0}}, addr};
      reg_req.wdata = 32'h0; // No write data for read operation
      reg_req.wstrb = 4'b0000; // No write strobe for read operation
      reg_req.write = 0; // Read operation
      reg_req.valid = 1; // Indicate valid request
      #10;
      while (!reg_rsp.ready) begin
        #1; // Wait for the register interface to be ready
      end
      data_out = reg_rsp.rdata; // Read data from the register interface
      reg_req.valid = 0; // Clear valid signal
      #10;

      if (data_out !== expected) begin
        $error("ERROR: Bus rdata - 0x%h: expected 0x%0h, got 0x%0h", reg_req.addr, expected, data_out);
      end else begin
        $display("PASS: Bus rdata - 0x%h: passed: got %0d (0x%h)", reg_req.addr, data_out, data_out);
      end
    end
  endtask



  // task write_reg(input logic [BlockAw-1:0] addr, input logic [3:0] wstrb, input logic [31:0] data);
  //   begin
  //     regbus_slave.addr = {{(WORD_WIDTH-BlockAw){1'b0}}, addr};
  //     regbus_slave.wdata = data;
  //     regbus_slave.wstrb = wstrb; // Write operation
  //     regbus_slave.write = 1;
  //     regbus_slave.valid = 1; // Indicate valid request
  //     #10;
  //     while (!regbus_slave.ready) begin
  //       #1; // Wait for the register interface to be ready
  //     end
  //     regbus_slave.write = 0; // Clear write signal
  //     regbus_slave.valid = 0; // Clear valid signal
  //   end
  // endtask

  // task assert_value(input logic [31:0] actual, input logic [31:0] expected, string message);
  //   if (expected !== actual) begin
  //     $error("ERROR: %s: expected 0x%0h, got 0x%0h", message, expected, actual);
  //   end else begin
  //     $display("PASS: %s passed: got %0d (0x%h)", message, actual, actual);
  //   end
  // endtask

  // task assert_read_reg(input logic [BlockAw-1:0] addr, input logic [31:0] expected);
  //   begin
  //     regbus_slave.addr = {{(WORD_WIDTH-BlockAw){1'b0}}, addr};
  //     regbus_slave.wdata = 32'h0; // No write data for read operation
  //     regbus_slave.wstrb = 4'b0000; // No write strobe for read operation
  //     regbus_slave.write = 0; // Read operation
  //     regbus_slave.valid = 1; // Indicate valid request
  //     #10;
  //     while (!regbus_slave.ready) begin
  //       #1; // Wait for the register interface to be ready
  //     end
  //     data_out = regbus_slave.rdata; // Read data from the register interface
  //     regbus_slave.valid = 0; // Clear valid signal
  //     #10;

  //     if (data_out !== expected) begin
  //       $error("ERROR: Bus rdata - 0x%h: expected 0x%0h, got 0x%0h", regbus_slave.addr, expected, data_out);
  //     end else begin
  //       $display("PASS: Bus rdata - 0x%h: passed: got %0d (0x%h)", regbus_slave.addr, data_out, data_out);
  //     end
  //   end
  // endtask

endmodule