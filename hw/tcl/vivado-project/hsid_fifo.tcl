create_project hsid_fifo ./vivado/hsid_fifo -part xc7a100tcsg324-1
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]
add_files {./hw/src/hsid_pkg/rtl/ ./hw/src/hsid_fifo/rtl/}
add_files -fileset sim_1 {./hw/src/hsid_fifo/tb/}
add_files -fileset constrs_1 ./hw/xdc/Nexys-A7-100T.xdc

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

exit