#!/bin/bash
set -e # Exit on error
# set -x # Enable verbose command output

show_help() {
  cat << EOF
Usage: $(basename "$0") [OPTIONS] MODULE_NAME [-- FUSESOC_ARGS...]

Run FuseSoC XSIM simulations for a given module.

Options:
  -g        Run XSIM in GUI mode.
  -w        Open waveform in GTKWave after simulation (batch mode only).
  -h        Show this help message.

Arguments:
  MODULE_NAME     Name of the module to simulate.

Examples:
  # Run simulation for 'hsid_divider' in batch mode
  $(basename "$0") hsid_divider

  # Run simulation and open waveform in GTKWave
  $(basename "$0") -w hsid_divider

  # Run simulation with XSIM GUI
  $(basename "$0") -g hsid_divider

  # Pass parameters to FuseSoC (everything after -- goes to FuseSoC)
  $(basename "$0") hsid_divider -- --help
  $(basename "$0") hsid_divider -- --K=32
EOF
}

SHOW_GUI=false
SHOW_WAVEFORM=false
while getopts "wgh" opt; do
  case $opt in
    w) SHOW_WAVEFORM=true ;;
    g) SHOW_GUI=true ;;
    h) show_help; exit 0 ;;
    \?) echo "Invalid option: -$OPTARG" >&2; show_help; exit 1 ;;
  esac
done

# Remove options from positional parameters
shift $((OPTIND - 1))

if [ $# -lt 1 ]; then
  echo "Error: MODULE_NAME is required."
  show_help
  exit 1
fi

MODULE_NAME="$1"
shift # drop module name, keep rest in "$@"

BASE_DIR=$(pwd)
WAVES=${BASE_DIR}/hw/waves

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_SIM_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/sim-xsim"

if [ "$SHOW_GUI" = true ]; then
  if [ ! -d "$FUSESOC_SIM_DIR" ]; then
    echo "Simulation directory $FUSESOC_SIM_DIR does not exist. Please run '$(basename "$0") $MODULE_NAME'."
    exit 1
  fi
  # Open xsim gui
  cd "$FUSESOC_SIM_DIR"
  make run-gui
else
  fusesoc run --no-export --target sim --tool xsim "$FUSESOC_NAME" "$@"
  if [ "$SHOW_WAVEFORM" = true ]; then
    sed -E 's/\$scope module ([^ ]+)\(.*\) /\$scope module \1 /' \
      "$FUSESOC_SIM_DIR/wave.vcd" > "$FUSESOC_SIM_DIR/cleaned.vcd"
    gtkwave "$FUSESOC_SIM_DIR/cleaned.vcd" "$WAVES/$MODULE_NAME.gtkw" \
      > /dev/null 2>&1 &
  else
    echo "Simulation completed. Use -w option to view waveform."
  fi
fi
