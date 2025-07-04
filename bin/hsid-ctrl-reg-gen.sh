#!/bin/env bash
set -e # Exit on error
# set -x # Enable verbose command output

# Get absolute path to the module directory
BASE_DIR=$(pwd)

NAME=hsid_x_ctrl_reg

REGTOOL=$BASE_DIR/hw/vendor/pulp_platform_register_interface/vendor/lowrisc_opentitan/util/regtool.py
HJSON_FILE=$BASE_DIR/hw/data/$NAME.hjson
RTL_DIR=$BASE_DIR/hw/src/$NAME
SW_DIR=$BASE_DIR/sw

mkdir -p $RTL_DIR $SW_DIR
printf -- "Generating control registers RTL...\n"
$REGTOOL -r -t $RTL_DIR $HJSON_FILE
printf -- "Generating software header...\n"
$REGTOOL --cdefines -o $SW_DIR/$NAME.h $HJSON_FILE
$REGTOOL -d $HJSON_FILE > $SW_DIR/$NAME.md
echo "" >> $SW_DIR/$NAME.h

## Copy vendor dependencies
# VENDOR=${BASE_DIR}/hw/vendor
# COMMON_CELLS=${VENDOR}/pulp_platform_common_cells
# REGISTER_INTERFACE=${VENDOR}/pulp_platform_register_interface
# LOWRISC_OPENTITAN=$REGISTER_INTERFACE/vendor/lowrisc_opentitan

# mkdir -p $RTL_DIR/common_cells
# cp -r $COMMON_CELLS/include/common_cells/*.svh $RTL_DIR/common_cells/
# mkdir -p $RTL_DIR/register_interface
# cp -R $REGISTER_INTERFACE/include/register_interface/*.svh $RTL_DIR/register_interface/
# cp -R $LOWRISC_OPENTITAN/src/*.sv $RTL_DIR