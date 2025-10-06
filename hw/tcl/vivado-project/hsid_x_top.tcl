create_project hsid_x_top ./vivado/hsid_x_top -part xc7a100tcsg324-1
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]

  # ./hw/deps/common_cells/src/binary_to_gray.sv 
  # ./hw/deps/common_cells/src/cb_filter_pkg.sv 
  # ./hw/deps/common_cells/src/cc_onehot.sv 
  # ./hw/deps/common_cells/src/cf_math_pkg.sv 
  # ./hw/deps/common_cells/src/clk_int_div.sv 
  # ./hw/deps/common_cells/src/credit_counter.sv 
  # ./hw/deps/common_cells/src/delta_counter.sv 
  # ./hw/deps/common_cells/src/ecc_pkg.sv 
  # ./hw/deps/common_cells/src/edge_propagator_tx.sv 
  # ./hw/deps/common_cells/src/exp_backoff.sv 
  # ./hw/deps/common_cells/src/fifo_v3.sv 
  # ./hw/deps/common_cells/src/gray_to_binary.sv 
  # ./hw/deps/common_cells/src/isochronous_4phase_handshake.sv 
  # ./hw/deps/common_cells/src/isochronous_spill_register.sv 
  # ./hw/deps/common_cells/src/lfsr.sv 
  # ./hw/deps/common_cells/src/lfsr_16bit.sv 
  # ./hw/deps/common_cells/src/lfsr_8bit.sv 
  # ./hw/deps/common_cells/src/multiaddr_decode.sv 
  # ./hw/deps/common_cells/src/mv_filter.sv 
  # ./hw/deps/common_cells/src/onehot_to_bin.sv 
  # ./hw/deps/common_cells/src/plru_tree.sv 
  # ./hw/deps/common_cells/src/passthrough_stream_fifo.sv 
  # ./hw/deps/common_cells/src/popcount.sv 
  # ./hw/deps/common_cells/src/rr_arb_tree.sv 
  # ./hw/deps/common_cells/src/rstgen_bypass.sv 
  # ./hw/deps/common_cells/src/serial_deglitch.sv 
  # ./hw/deps/common_cells/src/shift_reg.sv 
  # ./hw/deps/common_cells/src/shift_reg_gated.sv 
  # ./hw/deps/common_cells/src/spill_register_flushable.sv 
  # ./hw/deps/common_cells/src/stream_demux.sv 
  # ./hw/deps/common_cells/src/stream_filter.sv 
  # ./hw/deps/common_cells/src/stream_fork.sv 
  # ./hw/deps/common_cells/src/stream_intf.sv 
  # ./hw/deps/common_cells/src/stream_join.sv 
  # ./hw/deps/common_cells/src/stream_join_dynamic.sv 
  # ./hw/deps/common_cells/src/stream_mux.sv 
  # ./hw/deps/common_cells/src/stream_throttle.sv 
  # ./hw/deps/common_cells/src/sub_per_hash.sv 
  # ./hw/deps/common_cells/src/sync.sv 
  # ./hw/deps/common_cells/src/sync_wedge.sv 
  # ./hw/deps/common_cells/src/unread.sv 
  # ./hw/deps/common_cells/src/read.sv 
  # ./hw/deps/common_cells/src/cdc_reset_ctrlr_pkg.sv 
  # ./hw/deps/common_cells/src/addr_decode_dync.sv 
  # ./hw/deps/common_cells/src/cdc_2phase.sv 
  # ./hw/deps/common_cells/src/cdc_4phase.sv 
  # ./hw/deps/common_cells/src/cb_filter.sv 
  # ./hw/deps/common_cells/src/cdc_fifo_2phase.sv 
  # ./hw/deps/common_cells/src/counter.sv 
  # ./hw/deps/common_cells/src/ecc_decode.sv 
  # ./hw/deps/common_cells/src/ecc_encode.sv 
  # ./hw/deps/common_cells/src/edge_detect.sv 
  # ./hw/deps/common_cells/src/lzc.sv 
  # ./hw/deps/common_cells/src/max_counter.sv 
  # ./hw/deps/common_cells/src/rstgen.sv 
  # ./hw/deps/common_cells/src/spill_register.sv 
  # ./hw/deps/common_cells/src/stream_delay.sv 
  # ./hw/deps/common_cells/src/stream_fifo.sv 
  # ./hw/deps/common_cells/src/stream_fork_dynamic.sv 
  # ./hw/deps/common_cells/src/clk_mux_glitch_free.sv 
  # ./hw/deps/common_cells/src/addr_decode.sv 
  # ./hw/deps/common_cells/src/addr_decode_napot.sv 
  # ./hw/deps/common_cells/src/cdc_reset_ctrlr.sv 
  # ./hw/deps/common_cells/src/cdc_fifo_gray.sv 
  # ./hw/deps/common_cells/src/fall_through_register.sv 
  # ./hw/deps/common_cells/src/id_queue.sv 
  # ./hw/deps/common_cells/src/stream_to_mem.sv 
  # ./hw/deps/common_cells/src/stream_arbiter_flushable.sv 
  # ./hw/deps/common_cells/src/stream_fifo_optimal_wrap.sv 
  # ./hw/deps/common_cells/src/stream_register.sv 
  # ./hw/deps/common_cells/src/stream_xbar.sv 
  # ./hw/deps/common_cells/src/cdc_fifo_gray_clearable.sv 
  # ./hw/deps/common_cells/src/cdc_2phase_clearable.sv 
  # ./hw/deps/common_cells/src/mem_to_banks_detailed.sv 
  # ./hw/deps/common_cells/src/stream_arbiter.sv 
  # ./hw/deps/common_cells/src/stream_omega_net.sv 
  # ./hw/deps/common_cells/src/mem_to_banks.sv 
  # ./hw/deps/common_cells/src/edge_propagator_ack.sv 
  # ./hw/deps/common_cells/src/edge_propagator.sv 
  # ./hw/deps/common_cells/src/edge_propagator_rx.sv 
add_files {  
  ./hw/src/hsid_pkg/rtl/
  ./hw/deps/register_interface/vendor/lowrisc_opentitan/src/
  ./hw/deps/register_interface/src/
  ./hw/src/hsid_fifo/rtl/
  ./hw/src/hsid_divider/rtl/
  ./hw/src/hsid_mse_comp/rtl/
  ./hw/src/hsid_sq_df_acc/rtl/
  ./hw/src/hsid_x_ctrl_reg/rtl/
  ./hw/src/hsid_x_obi_mem/rtl/
  ./hw/src/hsid_mse/rtl/
  ./hw/src/hsid_x_registers/rtl/
  ./hw/src/hsid_main/rtl/
  ./hw/src/hsid_x_top/rtl/
}
add_files -fileset sim_1 { 
  ./hw/src/hsid_fifo/tb/
  ./hw/src/hsid_divider/tb/
  ./hw/src/hsid_sq_df_acc/tb/
  ./hw/src/hsid_mse/tb/
  ./hw/src/hsid_mse_comp/tb/
  ./hw/src/hsid_main/tb/
  ./hw/src/hsid_x_registers/tb/
  ./hw/src/hsid_x_obi_mem/tb/
  ./hw/src/hsid_x_top/tb/
}
add_files -fileset constrs_1   ./hw/xdc/Nexys-A7-100T.xdc

# Añadir include dirs para SystemVerilog (fuentes principales)
set_property include_dirs {
  ./hw/deps/common_cells/include
  ./hw/deps/register_interface/include
} [get_filesets sources_1]

# También para el testbench si los necesita
set_property include_dirs {
  ./hw/deps/common_cells/include
  ./hw/deps/register_interface/include
} [get_filesets sim_1]

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

set_property -name {xsim.simulate.runtime} -value {all} -objects [get_filesets sim_1]
set_property top hsid_x_top [current_fileset]
set_property top hsid_x_top_tb [get_filesets sim_1]

exit