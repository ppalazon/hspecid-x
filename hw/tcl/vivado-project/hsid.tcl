create_project 21_hsid ./vivado/21_hsid -part xc7a100tcsg324-1
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]
add_files {./src/00_hsid_pkg/ \
  ./src/01_fifo/rtl/ \
  ./src/01_sq_df_acc/rtl/ \
  ./src/20_mse/rtl/ \
  ./src/20_mse_comp/rtl/ \
  ./src/21_hsid/rtl/}
add_files -fileset sim_1 {./src/21_hsid/tb/}
add_files -fileset constrs_1 ./xdc/Nexys-A7-100T.xdc

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

exit