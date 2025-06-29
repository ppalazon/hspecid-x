create_project 01_sq_df_acc ./vivado/01_sq_df_acc -part xc7a100tcsg324-1
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]
add_files {./src/00_hsi_mse_pkg/ ./src/01_sq_df_acc/rtl/}
add_files -fileset sim_1 {./src/01_sq_df_acc/tb/}
add_files -fileset constrs_1 ./xdc/Nexys-A7-100T.xdc

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

exit