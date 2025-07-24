# HSpecID-X: A Hyperspectral Pixel Classifier Accelerator for X-HEEP Platforms

## Working environment

To work with this project you can configure your bash environment with `direnv`
application. You can read more about this tool on [direnv – unclutter your
.profile | direnv](https://direnv.net/)

By default, the configuration file `.envrc` is not on git repository because it
depends on your own computer. You can create your own `.envrc` file using the
following template:

```bash
layout python3

# Add scripts directory to PATH
export PATH=./bin:$PATH

# Set Vivado settings
export VIVADO_SETTINGS=/tools/Xilinx/Vivado/2024.2/settings64.sh
source $VIVADO_SETTINGS
```

## Vendor

https://github.com/esl-epfl/x-heep/tree/main/hw/vendor