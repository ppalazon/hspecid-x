# Development workflow

## Setting the environment

To work with this project you can configure your bash environment with `direnv`
application which sets all the necessary environment variables as you enter to
this project. You can read more about this tool on [direnv – unclutter your
.profile | direnv](https://direnv.net/)

By default, the configuration file `.envrc` is not on git repository because it
depends on your own set up. So, you should create your own `.envrc` file using
the following template:

```bash
layout python3

# Add scripts directory to PATH
export PATH=./bin:$PATH

# Set Vivado settings
export VIVADO_SETTINGS=/opt/vivado/settings64.sh
source $VIVADO_SETTINGS

# Set QuestaSim settings
export QUESTASIM_SETTINGS=/opt/questasim/setting.sh
export LM_LICENSE_FILE=
source $QUESTASIM_SETTINGS
```