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

BASE_DIR=$(pwd)
MODELSIM_DO=${BASE_DIR}/hw/tcl/modelsim-do

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_SIM_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/sim-modelsim"

# Check if FUSESOC_SIM_DIR exists
if [ ! -d "$FUSESOC_SIM_DIR" ]; then
  echo "Simulation directory $FUSESOC_SIM_DIR does not exist. Please run 'hsid-vsim $MODULE_NAME'."
  exit 1
fi

# Open modelsim gui
cd $FUSESOC_SIM_DIR
make run-gui

