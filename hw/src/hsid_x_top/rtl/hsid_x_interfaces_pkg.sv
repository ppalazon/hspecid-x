
// import obi_pkg::*;

// package hsid_x_interface_pkg;

//   // Register interface
//   typedef logic [31:0] addr_t; // Address type
//   typedef logic [31:0] data_t; // Data type
//   typedef logic [3:0] strb_t; // Strobe type

//   `REG_BUS_TYPEDEF_ALL(hsid_x_ri, addr_t, data_t, strb_t)

//   // OBI interface
//   localparam obi_cfg_t ObiDefaultConfig = obi_default_cfg(32, 32, 1, ObiMinimalOptionalConfig);
//   `OBI_TYPEDEF_DEFAULT_ALL(hsid_x_obi, ObiDefaultConfig)

// endpackage