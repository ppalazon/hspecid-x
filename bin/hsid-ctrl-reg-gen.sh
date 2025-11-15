#!/usr/bin/env bash
set -e # Exit on error
# set -x # Enable verbose command output

show_help() {
  cat << EOF
Usage: $(basename "$0") [OPTIONS]

Generate RTL and software headers for the hsid_x_ctrl registers using regtool.

Options:
  -h        Show this help message.

Environment:
  BASE_DIR   Base directory of the project (defaults to current working directory).

Description:
  This script runs the LowRISC regtool utility on the HJSON description file
  for 'hsid_x_ctrl', generating:
    - Verilog RTL register file
    - C header with register defines
    - Markdown documentation

Outputs are placed under:
  hw/src/hsid_x_ctrl_reg/rtl
  sw/
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

BASE_DIR=$(pwd)
NAME=hsid_x_ctrl

REGTOOL="$BASE_DIR/hw/deps/register_interface/vendor/lowrisc_opentitan/util/regtool.py"
HJSON_FILE="$BASE_DIR/data/$NAME.hjson"
RTL_DIR="$BASE_DIR/hw/src/${NAME}_reg/rtl"
SW_DIR="$BASE_DIR/sw"
DOCS_DIR="$BASE_DIR/docs"

# Check that regtool exists
if [ ! -f "$REGTOOL" ]; then
  echo "Error: regtool not found at $REGTOOL"
  exit 1
fi

# Check that HJSON file exists
if [ ! -f "$HJSON_FILE" ]; then
  echo "Error: HJSON file not found: $HJSON_FILE"
  exit 1
fi

mkdir -p "$RTL_DIR" "$SW_DIR"

printf -- "Generating control registers RTL...\n"
"$REGTOOL" -r -t "$RTL_DIR" "$HJSON_FILE"

printf -- "Generating software header...\n"
"$REGTOOL" --cdefines -o "$SW_DIR/${NAME}_reg.h" "$HJSON_FILE"

printf -- "Generating Markdown documentation...\n"
"$REGTOOL" -d "$HJSON_FILE" > "$DOCS_DIR/design/${NAME}_reg.md"

# Ensure header ends with newline
echo "" >> "$SW_DIR/${NAME}_reg.h"

echo "✅ Register generation completed."
