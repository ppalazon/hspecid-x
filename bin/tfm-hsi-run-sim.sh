#!/bin/bash
set -e # Exit on error
set -x # Enable verbose command output

SHOW_WAVEFORM=false
while getopts "w" opt; do
  case $opt in
    w) SHOW_WAVEFORM=true;;
    \?) echo "Invalid option: -$OPTARG" >&2 ;;
  esac
done

# Remove options from positional parameters
shift $((OPTIND - 1))

MODULE_NAME="$1"

# Check if module name is provided has a directory under code folder, if not exit
if [ -z "$MODULE_NAME" ]; then
  echo "Usage: $0 <module_name>"
  exit 1
fi

# Get absolute path to the module directory
BASE_DIR=$(pwd)
CODE=${BASE_DIR}/code
TCL=${BASE_DIR}/tcl
WAVES=${BASE_DIR}/waves

# Module configuration parameters
# Set testbench module name based on module type
case "$MODULE_NAME" in
    01_fifo)
        TESTBENCH_MODULE="fifo_tb"
        ;;
    01_sq_df)
        TESTBENCH_MODULE="sq_df_tb"
        ;;
    01_sq_df_acc)
        TESTBENCH_MODULE="sq_df_acc_tb"
        ;;
    10_vctr_fifo_full)
        TESTBENCH_MODULE="vctr_fifo_full_tb"
        ;;
    11_vctr_fifo_strm)
        TESTBENCH_MODULE="vctr_fifo_strm_tb"
        ;;
    12_mse_4)
        TESTBENCH_MODULE="mse_4_tb"
        ;;  
    20_hsi_mse)
        TESTBENCH_MODULE="hsi_mse_tb"
        ;;  
    20_hsi_mse_reg)
        TESTBENCH_MODULE="hsi_mse_reg_tb"
        ;;  
    20_hsi_mse_comp)
        TESTBENCH_MODULE="hsi_mse_comp_tb"
        ;; 
    21_hsi_mse_lib)
        TESTBENCH_MODULE="hsi_mse_lib_tb"
        ;;        
    *)
        echo "Module $MODULE_NAME is not supported for simulation."
        echo "Supported modules: 01_fifo, 01_sq_df, 01_sq_df_acc, 10_vctr_fifo_full, 11_vctr_fifo_strm, 12_mse_4"
        exit 1
        ;;
esac

rm -rf sim/$1
mkdir -p sim/$1
cd sim/$1

# Find all SystemVerilog files, but not in the testbench directory
SV_FILES=$(find "$CODE" -type f \( -name "*.sv" -o -name "*.vh" \) ! -path "*/tb/*" | sort)
TB_FILES=$CODE/$MODULE_NAME/tb/*.sv # Get module testbench files

# Set vivado environment variables
source $VIVADO_SETTINGS

xvlog --sv $SV_FILES $TB_FILES
xelab $TESTBENCH_MODULE -s testbench_sim
xsim testbench_sim -tclbatch $TCL/run_tb.tcl

if [ "$SHOW_WAVEFORM" = true ]; then
    gtkwave wave.vcd $WAVES/$MODULE_NAME.gtkw > /dev/null 2>&1 &
else
    echo "Simulation completed. Use -w option to view waveform."
fi