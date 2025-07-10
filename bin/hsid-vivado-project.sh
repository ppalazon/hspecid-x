#!/bin/bash
set -e # Exit on error
set -x # Enable verbose command output

MODULE_NAME="$1"

# Check if module name is provided has a directory under code folder, if not exit
if [ -z "$MODULE_NAME" ]; then
  echo "Usage: $0 <module_name>"
  exit 1
fi

# Get absolute path to the module directory
VIVADO_DIR=./vivado
TCL_DIR=./hw/tcl/vivado-project

# Set vivado environment variables
source $VIVADO_SETTINGS

mkdir -p ${VIVADO_DIR}
rm -rf ${VIVADO_DIR}/${MODULE_NAME}
vivado -mode tcl -source $TCL_DIR/$1.tcl -nojournal -nolog