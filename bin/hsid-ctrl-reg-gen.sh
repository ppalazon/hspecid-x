#!/bin/env bash
set -e # Exit on error
# set -x # Enable verbose command output

# Get absolute path to the module directory
BASE_DIR=$(pwd)

NAME=hsid_x

#REGTOOL=$BASE_DIR/hw/vendor/pulp_platform_register_interface/vendor/lowrisc_opentitan/util/regtool.py
REGTOOL=$BASE_DIR/hw/deps/register_interface/vendor/lowrisc_opentitan/util/regtool.py
HJSON_FILE=$BASE_DIR/data/$NAME.hjson
RTL_DIR=$BASE_DIR/hw/src/${NAME}_reg/rtl
SW_DIR=$BASE_DIR/sw

mkdir -p $RTL_DIR $SW_DIR
printf -- "Generating control registers RTL...\n"
$REGTOOL -r -t $RTL_DIR $HJSON_FILE
printf -- "Generating software header...\n"
$REGTOOL --cdefines -o $SW_DIR/${NAME}_reg.h $HJSON_FILE
$REGTOOL -d $HJSON_FILE > $SW_DIR/${NAME}_reg.md
echo "" >> $SW_DIR/${NAME}_reg.h