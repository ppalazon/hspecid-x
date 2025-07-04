# #!/bin/bash
# set -e # Exit on error
# # set -x # Enable verbose command output

# SHOW_WAVEFORM=false
# while getopts "w" opt; do
#   case $opt in
#     w) SHOW_WAVEFORM=true;;
#     \?) echo "Invalid option: -$OPTARG" >&2 ;;
#   esac
# done

# # Remove options from positional parameters
# shift $((OPTIND - 1))

# MODULE_NAME="$1"

# # Check if module name is provided has a directory under code folder, if not exit
# if [ -z "$MODULE_NAME" ]; then
#   echo "Usage: $0 <module_name>"
#   exit 1
# fi

# # Get absolute path to the module directory
# BASE_DIR=$(pwd)
# SRC=${BASE_DIR}/hw/src
# TCL=${BASE_DIR}/hw/tcl
# WAVES=${BASE_DIR}/hw/waves
# VENDOR=${BASE_DIR}/hw/vendor


# # Module configuration parameters
# # Set testbench module name based on module type
# case "$MODULE_NAME" in
#     01_fifo)
#         TESTBENCH_MODULE="fifo_tb"
#         ;;
#     01_sq_df)
#         TESTBENCH_MODULE="sq_df_tb"
#         ;;
#     01_sq_df_acc)
#         TESTBENCH_MODULE="sq_df_acc_tb"
#         ;;
#     10_vctr_fifo_full)
#         TESTBENCH_MODULE="vctr_fifo_full_tb"
#         ;;
#     11_vctr_fifo_strm)
#         TESTBENCH_MODULE="vctr_fifo_strm_tb"
#         ;;
#     12_mse_batch)
#         TESTBENCH_MODULE="mse_4_tb"
#         ;;  
#     20_mse)
#         TESTBENCH_MODULE="mse_tb"
#         ;;  
#     20_mse_reg)
#         TESTBENCH_MODULE="mse_reg_tb"
#         ;;  
#     20_mse_comp)
#         TESTBENCH_MODULE="mse_comp_tb"
#         ;; 
#     21_hsid)
#         TESTBENCH_MODULE="hsid_tb"
#         ;;        
#     *)
#         echo "Module $MODULE_NAME is not supported for simulation."
#         echo "Supported modules: 01_fifo, 01_sq_df, 01_sq_df_acc, 10_vctr_fifo_full, 11_vctr_fifo_strm, 12_mse_batch"
#         exit 1
#         ;;
# esac

# rm -rf build/sim/$1
# mkdir -p build/sim/$1
# cd build/sim/$1

# # Vendor dpendencies
# COMMON_CELLS=${VENDOR}/pulp_platform_common_cells
# REGISTER_INTERFACE=${VENDOR}/pulp_platform_register_interface
# LOWRISC_OPENTITAN=$REGISTER_INTERFACE/vendor/lowrisc_opentitan

# # Find all SystemVerilog files, but not in the testbench directory
# SV_FILES=$(find "$SRC" -type f \( -name "*.sv" -o -name "*.vh" \) ! -path "*/tb/*" | sort)
# # VENDOR_FILES="$COMMON_CELLS/include/common_cells/*.svh $REGISTER_INTERFACE/include/register_interface/*.svh $LOWRISC_OPENTITAN/src/*.sv" 
# TB_FILES=$SRC/$MODULE_NAME/tb/*.sv # Get module testbench files

# # Set vivado environment variables
# source $VIVADO_SETTINGS

# xvlog --sv $SV_FILES $TB_FILES
# xelab $TESTBENCH_MODULE -s testbench_sim
# xsim testbench_sim -tclbatch $TCL/run_tb.tcl

# if [ "$SHOW_WAVEFORM" = true ]; then
#     gtkwave wave.vcd $WAVES/$MODULE_NAME.gtkw > /dev/null 2>&1 &
# else
#     echo "Simulation completed. Use -w option to view waveform."
# fi