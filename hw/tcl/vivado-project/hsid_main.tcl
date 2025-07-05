create_project hsid_main ./vivado/hsid_main -part xc7a100tcsg324-1
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]
add_files {./src/00_hsid_pkg/ \
  ./src/hsid_fifo/rtl/ \
  ./src/hsid_sq_df_acc/rtl/ \
  ./src/hsid_mse/rtl/ \
  ./src/hsid_mse_comp/rtl/ \
  ./src/hsid_main/rtl/}
add_files -fileset sim_1 {./src/hsid_main/tb/}
add_files -fileset constrs_1 ./xdc/Nexys-A7-100T.xdc

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

exit