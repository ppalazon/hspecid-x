#!/bin/bash
set -e # Exit on error
# set -x # Enable verbose command output

SHOW_GUI=false
SHOW_WAVEFORM=false

print_help() {
  cat << EOF
Usage: hsid-sim-simple [options] <module_name>

Runs a FuseSoC/XSim proof of concept for the specified module.
Optionally opens the XSim GUI or the waveform viewer after simulation.

Options:
  -g        Open the XSim GUI for the given module.
  -w        Open GTKWave with the waveform after simulation.
  -h        Show this help message.

Arguments:
  <module_name>
            Name of the hardware module to simulate.
            Required unless -g is used on an already built simulation.

Behavior:
  - If -g is provided:
        Opens the XSim GUI in:
          build/uclm_hspecidx_<module_name>_0/sim-simple-xsim
        Requires a prior build (run: hsid-xsim <module_name>).

  - If -w is provided:
        After simulation, cleans the VCD file and opens GTKWave using:
          hw/waves/<module_name>-simple.gtkw

Examples:
  hsid-xsim mymodule
        Run simulation for "mymodule" using FuseSoC.

  hsid-xsim -w mymodule
        Run simulation and open GTKWave afterwards.

  hsid-xsim -g mymodule
        Open XSim GUI for a previously built simulation.

Notes:
  - Simulation VCD is generated at:
        build/uclm_hspecidx_<module_name>_0/sim-simple-xsim/wave.vcd
  - GUI mode requires the simulation directory to already exist.
EOF
}

while getopts "wgh" opt; do
  case $opt in
    w) SHOW_WAVEFORM=true;;
    g) SHOW_GUI=true;;
    h) print_help; exit 0;;
    \?) echo "Invalid option: -$OPTARG" >&2; print_help; exit 1;;
  esac
done

# Remove options from positional parameters
shift $((OPTIND - 1))

MODULE_NAME="$1"

# If no module_name is given and not in GUI mode, show help
if [ -z "$MODULE_NAME" ] && [ "$SHOW_GUI" = false ]; then
  echo "Error: <module_name> is required."
  echo
  print_help
  exit 1
fi

BASE_DIR=$(pwd)
WAVES=${BASE_DIR}/hw/waves

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_SIM_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/sim-simple-xsim"

if [ "$SHOW_GUI" = true ]; then
  if [ ! -d "$FUSESOC_SIM_DIR" ]; then
    echo "Simulation directory $FUSESOC_SIM_DIR does not exist. Please run 'hsid-xsim $MODULE_NAME'."
    exit 1
  fi

  # Open xsim gui
  cd "$FUSESOC_SIM_DIR"
  make run-gui
else
  fusesoc run --no-export --target sim-simple --tool xsim "$@"
  if [ "$SHOW_WAVEFORM" = true ]; then
    sed -E 's/\$scope module ([^ ]+)\(.*\) /\$scope module \1 /' \
      "$FUSESOC_SIM_DIR/wave.vcd" > "$FUSESOC_SIM_DIR/cleaned.vcd"
    gtkwave "$FUSESOC_SIM_DIR/cleaned.vcd" "$WAVES/$MODULE_NAME-simple.gtkw" > /dev/null 2>&1 &
  else
    echo "Simulation completed. Use -w option to view waveform."
  fi
fi