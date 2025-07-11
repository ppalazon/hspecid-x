`timescale 1ns / 1ps

module hsid_x_top #(
    parameter WORD_WIDTH = 32,  // Width of the word in bits
    parameter DATA_WIDTH = 16,  // 16 bits by default
    parameter DATA_WIDTH_MUL = 32,  // Data width for multiplication, larger than WORD_WIDTH
    parameter DATA_WIDTH_ACC = 48,  // Data width for accumulator, larger than WORD
    parameter HSI_BANDS = 254,  // Number of HSI bands
    parameter HSI_LIBRARY_SIZE = 4095,  // Size of the HSI library
    parameter BUFFER_LENGTH = 4,  // Number of entries in the FIFO buffer
    parameter ELEMENTS = HSI_BANDS / 2, // Number of elements in the vector
    localparam HSI_BANDS_ADDR = $clog2(HSI_BANDS),  // Address width for HSI bands
    localparam HSI_LIBRARY_SIZE_ADDR = $clog2(HSI_LIBRARY_SIZE)
  ) (
    input logic clk,
    input logic rst_n,

    // Register interface
    input hsid_x_reg_pkg::reg_req_t reg_req_i,
    output hsid_x_reg_pkg::reg_rsp_t reg_rsp_o,

    // OBI interface (Master)
    input hsid_x_obi_inf_pkg::obi_resp_t obi_rsp_i,
    output hsid_x_obi_inf_pkg::obi_req_t obi_req_o,

    // Interrupt interface
    output logic hsid_x_int_o
  );

  localparam ELEMENTS_ADDR = $clog2(ELEMENTS);  // Address width

  typedef enum logic [2:0] {
    IDLE, START_READ_CAPTURED, READ_CAPTURED, START_READ_LIBRARY, READ_LIBRARY
  } hsid_x_obi_read_t;

  logic start;
  logic clear;
  logic idle;
  logic ready;
  logic done;
  logic error;

  logic [HSI_LIBRARY_SIZE_ADDR-1:0] library_size;
  logic [HSI_BANDS_ADDR-1:0] pixel_bands;
  logic [WORD_WIDTH-1:0] captured_pixel_addr;
  logic [WORD_WIDTH-1:0] library_pixel_addr;

  logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_min_ref; // Pixel reference for minimum MSE value
  logic [WORD_WIDTH-1:0] mse_min_value;  // Minimum MSE
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] mse_max_ref;  // Pixel reference for maximum MSE value
  logic [WORD_WIDTH-1:0] mse_max_value;  // Maximum MSE

  // Obi wires
  logic [WORD_WIDTH-1:0] obi_initial_addr;
  logic [HSI_LIBRARY_SIZE_ADDR-1:0] obi_limit_in;
  logic obi_data_out_valid;
  logic [WORD_WIDTH-1:0] obi_data_out;
  logic obi_start;
  wire obi_done;

  // Elements bands
  logic [ELEMENTS_ADDR-1:0] elements_bands;

  // Assign Interrupt output
  assign hsid_x_int_o = done;
  assign elements_bands = (pixel_bands / 2);

  hsid_x_obi_read_t current_state = IDLE, next_state = START_READ_CAPTURED;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
      error <= 1'b0;  // Reset error flag
      obi_initial_addr <= 0;
      obi_limit_in <= 1;
      obi_start <= 1'b0;
    end else begin
      current_state <= next_state;  // Update current state
      error <= 1'b0;  // Reset error flag
      if (current_state == IDLE) begin
        obi_initial_addr <= 0;
        obi_limit_in <= 1;
        obi_start <= 1'b0;
      end else if (current_state == START_READ_CAPTURED) begin
        obi_initial_addr <= captured_pixel_addr;
        obi_limit_in <= { {(HSI_LIBRARY_SIZE_ADDR-ELEMENTS_ADDR){1'b0}}, elements_bands };
        obi_start <= 1'b1;
      end else if (current_state == READ_CAPTURED) begin
        obi_start <= 1'b0;
      end else if (current_state == START_READ_LIBRARY) begin
        obi_initial_addr <= library_pixel_addr;
        obi_limit_in <= elements_bands * library_size;
        obi_start <= 1'b1;
      end else if (current_state == READ_LIBRARY) begin
        obi_start <= 1'b1;
      end
    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        next_state = start ? START_READ_CAPTURED : IDLE;
      end
      START_READ_CAPTURED: begin
        next_state = READ_CAPTURED;
      end
      READ_CAPTURED: begin
        next_state = obi_done ? START_READ_LIBRARY : READ_CAPTURED;
      end
      START_READ_LIBRARY: begin
        next_state = READ_LIBRARY;
      end
      READ_LIBRARY: begin
        next_state = obi_done ? IDLE : READ_LIBRARY;
      end
      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // Register interface to hardware interface
  hsid_x_ctrl_reg #(
    .HSI_BANDS(HSI_BANDS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE),
    .WORD_WIDTH(WORD_WIDTH)
  ) hsid_x_ctrl_reg (
    .clk(clk),
    .rst_n(rst_n),
    .reg_req(reg_req_i),
    .reg_rsp(reg_rsp_o),
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

  // OBI interface to memory interface
  hsid_x_obi_mem #(
    .WORD_WIDTH      (WORD_WIDTH),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  )
  u_hsid_x_obi_mem (
    .clk           (clk),
    .data_out      (obi_data_out),
    .data_out_valid(obi_data_out_valid),
    .done          (obi_done),
    .idle          (),
    .initial_addr  (obi_initial_addr),
    .limit         (obi_limit_in),
    .obi_req       (obi_req_o),
    .obi_rsp       (obi_rsp_i),
    .ready         (),
    .rst_n         (rst_n),
    .start         (obi_start)
  );

  // HSID Main module instantiation
  hsid_main #(
    .WORD_WIDTH      (WORD_WIDTH),
    .DATA_WIDTH      (DATA_WIDTH),
    .DATA_WIDTH_MUL  (DATA_WIDTH_MUL),
    .DATA_WIDTH_ACC  (DATA_WIDTH_ACC),
    .HSI_BANDS       (HSI_BANDS),
    .BUFFER_LENGTH   (BUFFER_LENGTH),
    .ELEMENTS        (ELEMENTS),
    .HSI_LIBRARY_SIZE(HSI_LIBRARY_SIZE)
  )
  u_hsid_main (
    // Clear signal to reset MSE values
    .clear            (clear),
    .clk              (clk),
    .done             (done),
    .hsi_bands_in     (pixel_bands),
    .hsi_vctr_in      (obi_data_out),
    .hsi_vctr_in_valid(obi_data_out_valid),
    .idle             (idle),
    .library_size_in  (library_size),
    .mse_max_ref      (mse_max_ref),
    .mse_max_value    (mse_max_value),
    .mse_min_ref      (mse_min_ref),
    .mse_min_value    (mse_min_value),
    .ready            (ready),
    .rst_n            (rst_n),
    .start            (start)
  );



endmodule