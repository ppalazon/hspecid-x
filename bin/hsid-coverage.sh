#!/bin/bash
set -e # Exit on error
set -x # Enable verbose command output

MODULE_NAME="$1"

BASE_DIR=$(pwd)
MODELSIM_DO=${BASE_DIR}/hw/tcl/modelsim-do

FUSESOC_NAME="uclm:hspecidx:${MODULE_NAME}"
FUSESOC_COVERAGE_DIR="build/uclm_hspecidx_${MODULE_NAME}_0/coverage-modelsim"

fusesoc run --no-export --target coverage $FUSESOC_NAME

rm -rf reports/$MODULE_NAME
mkdir -p reports/$MODULE_NAME
cp -r $FUSESOC_COVERAGE_DIR/report/* reports/$MODULE_NAME

./bin/hsid-report-sva2tex.py $MODULE_NAME
./bin/hsid-report-code2tex.py $MODULE_NAME
./bin/hsid-report-cvg2tex.py $MODULE_NAME