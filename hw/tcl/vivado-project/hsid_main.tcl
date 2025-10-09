create_project hsid_main ./vivado/hsid_main -part xc7a100tcsg324-1
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]
add_files {
  ./hw/src/hsid_pkg/rtl/hsid_pkg.sv
  ./hw/src/hsid_fifo/rtl/ 
  ./hw/src/hsid_divider/rtl/ 
  ./hw/src/hsid_sq_df_acc/rtl/ 
  ./hw/src/hsid_mse/rtl/ 
  ./hw/src/hsid_mse_comp/rtl/ 
  ./hw/src/hsid_main/rtl/
}
add_files -fileset sim_1 {
  ./hw/src/hsid_rst_sync/rtl/
  ./hw/src/hsid_fifo/tb/
  ./hw/src/hsid_divider/tb/
  ./hw/src/hsid_sq_df_acc/tb/
  ./hw/src/hsid_mse/tb/
  ./hw/src/hsid_mse_comp/tb/
  ./hw/src/hsid_main/tb/
}
add_files -fileset constrs_1 ./hw/xdc/Nexys-A7-100T.xdc

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

set_property -name {xsim.simulate.runtime} -value {all} -objects [get_filesets sim_1]
set_property top hsid_main [current_fileset]
set_property top hsid_main_simple_tb [get_filesets sim_1]

set top "hsid_main_simple_tb"

# current_wave_config new_wave_config
# add_wave -into [add_wave_group "DUT"] [get_objects /$top/dut/*]
# add_wave -group FSM [get_objects /$top/dut/fsm/*]
# add_wave -group MSE [get_objects /$top/dut/mse/*]
# add_wave -group {SqDfAcc 1} [get_objects /$top/dut/mse/channel_1/*]
# add_wave -group {SqDfAcc 2} [get_objects /$top/dut/mse/channel_2/*]
# add_wave -group Divider [get_objects /$top/dut/mse/divider/*]
# add_wave -group {MSE Comp} [get_objects /$top/dut/mse_comp/*]
# add_wave -group {FIFO Cap} [get_objects /$top/dut/fifo_captured/*]
# add_wave -group {FIFO Ref} [get_objects /$top/dut/fifo_ref/*]

exit