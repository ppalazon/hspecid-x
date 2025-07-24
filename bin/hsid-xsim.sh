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
WAVES=${BASE_DIR}/hw/waves

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_SIM_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/sim-xsim"

fusesoc run --no-export --target sim --tool xsim $FUSESOC_NAME

if [ "$SHOW_WAVEFORM" = true ]; then
  sed -E 's/\$scope module ([^ ]+)\(.*\) /\$scope module \1 /' $FUSESOC_SIM_DIR/wave.vcd > $FUSESOC_SIM_DIR/cleaned.vcd
  gtkwave $FUSESOC_SIM_DIR/cleaned.vcd $WAVES/$MODULE_NAME.gtkw > /dev/null 2>&1 &
else
  echo "Simulation completed. Use -w option to view waveform."
fi