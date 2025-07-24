#!/bin/bash
set -e # Exit on error
set -x # Enable verbose command output

MODULE_NAME="$1"

BASE_DIR=$(pwd)
WAVES=${BASE_DIR}/hw/waves

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_SIM_DIR="build/uclm_hspecidx_${MODULE_NAME}/sim-modelsim"

fusesoc run --no-export --target sim --tool modelsim $FUSESOC_NAME

