// Copyright 2022 OpenHW Group
// Solderpad Hardware License, Version 2.1, see LICENSE.md for details.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
/*
 *
 * Description: OBI package, contains common system definitions.
 * This file has been copied from X-HEEP repository (hw/core-v-mini-mcu/include/obi_pkg.sv)
 *
 */

package hsid_x_obi_inf_pkg;

  typedef struct packed {
    logic        req;
    logic        we;
    logic [3:0]  be;
    logic [31:0] addr;
    logic [31:0] wdata;
  } obi_req_t;

  typedef struct packed {
    logic        gnt;
    logic        rvalid;
    logic [31:0] rdata;
  } obi_resp_t;

endpackage