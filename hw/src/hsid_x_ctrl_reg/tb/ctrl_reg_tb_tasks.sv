package ctrl_reg_tb_tasks;

  import hsid_pkg::*;
  import hsid_x_ctrl_reg_pkg::*;
  import hsid_x_reg_pkg::*;

  localparam WORD_WIDTH = HSID_WORD_WIDTH;

  function [WORD_WIDTH-1:0] addr_reg(input hsid_x_ctrl_id_e ctrl_id);
    logic [BlockAw-1:0] addr;
    case (ctrl_id)
      HSID_X_CTRL_STATUS: addr = HSID_X_CTRL_STATUS_OFFSET;
      HSID_X_CTRL_LIBRARY_SIZE: addr = HSID_X_CTRL_LIBRARY_SIZE_OFFSET;
      HSID_X_CTRL_PIXEL_BANDS: addr = HSID_X_CTRL_PIXEL_BANDS_OFFSET;
      HSID_X_CTRL_CAPTURED_PIXEL_ADDR: addr = HSID_X_CTRL_CAPTURED_PIXEL_ADDR_OFFSET;
      HSID_X_CTRL_LIBRARY_PIXEL_ADDR: addr = HSID_X_CTRL_LIBRARY_PIXEL_ADDR_OFFSET;
      HSID_X_CTRL_MSE_MIN_REF: addr = HSID_X_CTRL_MSE_MIN_REF_OFFSET;
      HSID_X_CTRL_MSE_MAX_REF: addr = HSID_X_CTRL_MSE_MAX_REF_OFFSET;
      HSID_X_CTRL_MSE_MIN_VALUE: addr = HSID_X_CTRL_MSE_MIN_VALUE_OFFSET;
      HSID_X_CTRL_MSE_MAX_VALUE: addr = HSID_X_CTRL_MSE_MAX_VALUE_OFFSET;
    endcase
    return {{(WORD_WIDTH-BlockAw){1'b0}}, addr};
  endfunction

  task automatic write_reg(
      ref reg_req_t reg_req, input hsid_x_ctrl_id_e ctrl_id, logic [31:0] data
    );
    begin
      reg_req.addr = addr_reg(ctrl_id);
      reg_req.wdata = data;
      reg_req.wstrb = HSID_X_CTRL_PERMIT[ctrl_id]; // Write operation
      reg_req.write = 1;
      reg_req.valid = 1; // Indicate valid request
      #10;
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

  task automatic read_reg(
      ref reg_req_t reg_req, input hsid_x_ctrl_id_e ctrl_id
    );
    logic [WORD_WIDTH-1:0] data_out;
    begin
      reg_req.addr = addr_reg(ctrl_id);
      reg_req.wdata = 32'h0; // No write data for read operation
      reg_req.wstrb = 4'b0000; // No write strobe for read operation
      reg_req.write = 0; // Read operation
      reg_req.valid = 1; // Indicate valid request
      #10;
      reg_req.valid = 0; // Clear valid signal
    end
  endtask

endpackage