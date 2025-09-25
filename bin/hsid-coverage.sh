#!/bin/bash
set -e # Exit on error
set -x # Enable verbose command output

show_help() {
  cat << EOF
Usage: $(basename "$0") MODULE_NAME [-- FUSESOC_ARGS...]

Run FuseSoC coverage simulation for a given module and generate reports.

Options:
  -h        Show this help message.

Arguments:
  MODULE_NAME     Name of the module to analyze.

Examples:
  # Run coverage simulation for 'hsid_divider'
  $(basename "$0") hsid_divider

  # Run coverage simulation and pass parameters to FuseSoC
  $(basename "$0") hsid_divider -- --help
  $(basename "$0") hsid_divider -- --K=32
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

if [ $# -lt 1 ]; then
  echo "Error: MODULE_NAME is required."
  show_help
  exit 1
fi

MODULE_NAME="$1"
shift # drop module name, keep rest in "$@"

BASE_DIR=$(pwd)
MODELSIM_DO=${BASE_DIR}/hw/tcl/modelsim-do

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_COVERAGE_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/coverage-modelsim"

# Run coverage simulation (forward extra args to fusesoc)
fusesoc run --no-export --target coverage "$FUSESOC_NAME" "$@"

# Collect reports
rm -rf "reports/$MODULE_NAME"
mkdir -p "reports/$MODULE_NAME"
cp -r "$FUSESOC_COVERAGE_DIR/report/"* "reports/$MODULE_NAME"

# Generate TeX reports
# ./bin/hsid-report-sva2tex.py "$MODULE_NAME"
# ./bin/hsid-report-code2tex.py "$MODULE_NAME"
# ./bin/hsid-report-cvg2tex.py "$MODULE_NAME"
