#!/bin/bash
set -e # Exit on error
# set -x # Enable verbose command output

show_help() {
  cat << EOF
Usage: $(basename "$0") MODULE_NAME

Run Vivado in batch mode with the TCL script for the specified module.

Options:
  -h        Show this help message.

Arguments:
  MODULE_NAME     Name of the module (must match a .tcl file under hw/tcl/vivado-project).

Environment:
  VIVADO_SETTINGS   Path to Vivado settings script (must be set before running).

Examples:
  # Run Vivado project generation for 'hsid_divider'
  $(basename "$0") hsid_divider
EOF
}

# Parse options
while getopts "h" opt; do
  case $opt in
    h) show_help; exit 0 ;;
    \?) echo "Invalid option: -$OPTARG" >&2; show_help; exit 1 ;;
  esac
done

shift $((OPTIND - 1))

MODULE_NAME="$1"

if [ -z "$MODULE_NAME" ]; then
  echo "Error: MODULE_NAME is required."
  show_help
  exit 1
fi

VIVADO_DIR=./vivado
TCL_DIR=./hw/tcl/vivado-project

# Check Vivado settings
if [ -z "$VIVADO_SETTINGS" ]; then
  echo "Error: VIVADO_SETTINGS environment variable is not set."
  echo "Please export VIVADO_SETTINGS to point to your Vivado settings script."
  exit 1
fi

if [ ! -f "$TCL_DIR/$MODULE_NAME.tcl" ]; then
  echo "Error: TCL script not found: $TCL_DIR/$MODULE_NAME.tcl"
  exit 1
fi

# Set Vivado environment variables
source "$VIVADO_SETTINGS"

mkdir -p "$VIVADO_DIR"
rm -rf "$VIVADO_DIR/$MODULE_NAME"

vivado -mode tcl -source "$TCL_DIR/$MODULE_NAME.tcl" -nojournal -nolog
