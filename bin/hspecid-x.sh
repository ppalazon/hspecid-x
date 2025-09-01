#!/bin/bash
set -e # Exit on error
#set -x # Enable verbose command output

SHOW_WAVEFORM=""
HSP_BANDS=10
HSP_LIBRARY_SIZE=2
RND_GNT=0
while getopts "wrb:l:" opt; do
  case $opt in
    w) SHOW_WAVEFORM="-w";;
    r) RND_GNT=1;;
    b) HSP_BANDS=$OPTARG;;
    l) HSP_LIBRARY_SIZE=$OPTARG;;
    \?) echo "Invalid option: -$OPTARG" >&2 ;;
  esac
done

echo "Remember: Max HSP_BANDS=127, Max HSP_LIBRARY_SIZE=63"
echo "HSP_BANDS=$HSP_BANDS"
echo "HSP_LIBRARY_SIZE=$HSP_LIBRARY_SIZE"
echo "RND_GNT=$RND_GNT"

hsid-sim-simple.sh $SHOW_WAVEFORM hsid_x_top --TEST_HSP_BANDS=$HSP_BANDS --TEST_HSP_LIBRARY_SIZE=$HSP_LIBRARY_SIZE --TEST_RND_GNT=$RND_GNT