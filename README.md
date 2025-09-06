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

## License

This project is licensed under the **CERN-OHL-P v2** (Permissive).  
You are free to use, modify, and distribute this design, provided that the copyright
notice and license text are retained.  

See the [LICENSE](./LICENSE) file for details.  
More information about CERN-OHL-P v2 can be found at the [CERN OHL website](https://cern-ohl.web.cern.ch/).

## Third-Party Components

- **common_cells** – licensed under [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
- **register_interface** – licensed under [Solderpad Hardware License v0.51](http://solderpad.org/licenses/SHL-0.51/).
- **obi** – [Solderpad Hardware License v0.51](http://solderpad.org/licenses/SHL-0.51/).

Original licenses and attributions are retained in their respective files and headers.