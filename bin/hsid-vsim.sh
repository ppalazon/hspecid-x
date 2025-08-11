#!/bin/bash
set -e # Exit on error
set -x # Enable verbose command output

SHOW_GUI=false
while getopts "g" opt; do
  case $opt in
    g) SHOW_GUI=true;;
    \?) echo "Invalid option: -$OPTARG" >&2 ;;
  esac
done

# Remove options from positional parameters
shift $((OPTIND - 1))

MODULE_NAME="$1"

BASE_DIR=$(pwd)
MODELSIM_DO=${BASE_DIR}/hw/tcl/modelsim-do

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_SIM_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/sim-modelsim"


if [ "$SHOW_GUI" = true ]; then
  if [ ! -d "$FUSESOC_SIM_DIR" ]; then
    echo "Simulation directory $FUSESOC_SIM_DIR does not exist. Please run 'hsid-vsim $MODULE_NAME'."
    exit 1
  fi

  # Open modelsim gui
  cd $FUSESOC_SIM_DIR
  make run-gui
else
  fusesoc run --no-export --target sim --tool modelsim $FUSESOC_NAME
fi