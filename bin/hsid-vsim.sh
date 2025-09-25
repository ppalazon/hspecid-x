#!/bin/bash
set -e # Exit on error
# set -x # Enable verbose command output

show_help() {
  cat << EOF
Usage: $(basename "$0") [OPTIONS] MODULE_NAME [-- FUSESOC_ARGS...]

Run FuseSoC ModelSim simulations for a given module.

Options:
  -g        Run ModelSim in GUI mode.
  -h        Show this help message.

Arguments:
  MODULE_NAME     Name of the module to simulate.

Examples:
  # Run simulation for 'hsid_divider' in batch mode
  $(basename "$0") hsid_divider

  # Run simulation with ModelSim GUI
  $(basename "$0") -g hsid_divider

  # Pass parameters to FuseSoC (everything after -- goes to FuseSoC)
  $(basename "$0") hsid_divider -- --help
  $(basename "$0") hsid_divider -- --K=32
EOF
}

SHOW_GUI=false
while getopts "gh" opt; do
  case $opt in
    g) SHOW_GUI=true;;
    h) show_help; exit 0 ;;
    \?) echo "Invalid option: -$OPTARG" >&2 ;;
  esac
done

# Remove options from positional parameters
shift $((OPTIND - 1))

# Getting module name
MODULE_NAME="$1"
shift # drop the module name, keep rest in "$@"

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
  fusesoc run --no-export --target sim --tool modelsim $FUSESOC_NAME "$@"
fi