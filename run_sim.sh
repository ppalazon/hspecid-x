#!/bin/bash

# Set vivado environment variables
source /tools/Xilinx/Vivado/2024.2/settings64.sh

MODULE_NAME="$1"
TESTBENCH_MODULE="$2"


# Check if module name is provided has a directory under code folder, if not exit
if [ -z "$MODULE_NAME" ]; then
  echo "Usage: $0 <module_name>"
  exit 1
fi
if [ ! -d "code/$MODULE_NAME" ]; then
  echo "Module $MODULE_NAME does not exist in the code directory."
  exit 1
fi

mkdir -p sim/$1
cd sim/$1
MD="../../code/$1"

xvlog --sv $MD/rtl/*.sv $MD/tb/*.sv
xelab $TESTBENCH_MODULE -s testbench_sim
xsim testbench_sim --runall