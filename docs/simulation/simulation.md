## Execution of the Testbenches

The *testbenches* for each module developed in this project are executed using
FuseSoC. Each module is configured to support simulation with both Vivado
(`xsim`) and Siemens QuestaSim (`vsim`).

### Simulation with `xsim`

To start a simulation using `xsim`, run the command shown in the listing below.
The terminal output will display informational messages and any errors that may
occur. To run the *testbench* of a different module, simply pass the module code
as a parameter.

```bash
fusesoc run --target sim --tool xsim hsid_x_top
```

A Bash *script* is provided to simplify execution and debugging with GTKWave.
This script serves as a lightweight *wrapper* around FuseSoC, with several
default options. It is located in the project’s `bin` directory, and its
available execution options are shown in the listing below. As with FuseSoC, the
*testbench* of any module can be executed by passing it as an argument.

```bash
# General form (from repo root)
bin/hsid-xsim.sh [OPTIONS] MODULE_NAME [-- FUSESOC_ARGS...]

# Examples
bin/hsid-xsim.sh hsid_x_top      # Only simulation
bin/hsid-xsim.sh -w hsid_x_top   # Simulation and open GTKWave waveform
bin/hsid-xsim.sh -g hsid_x_top   # Open Vivado environment (only simulation)
bin/hsid-xsim.sh -h              # Show help
```

To accelerate debugging in GTKWave, signal groups are automatically loaded
according to the configuration file `hw/waves/hsid_x_top.gtkw`.

You can simulate and obtain the waveform of any module listed in the table below:

| Module                                              | Simulate with `xsim` and open `GTKWave` |
| --------------------------------------------------- | --------------------------------------- |
| [`hsid_fifo`](../design/hsid_fifo.md)               | `hsid-xsim.sh -w hsid_fifo`             |
| [`hsid_sq_df_acc`](../design/hsid_sq_df_acc.md)     | `hsid-xsim.sh -w hsid_sq_df_acc`        |
| [`hsid_divisor`](../design/hsid_divider.md)         | `hsid-xsim.sh -w hsid_divisor`          |
| [`hsid_mse`](../design/hsid_mse.md)                 | `hsid-xsim.sh -w hsid_mse`              |
| [`hsid_mse_comp`](../design/hsid_mse_comp.md)       | `hsid-xsim.sh -w hsid_mse_comp`         |
| [`hsid_main`](../design/hsid_main.md)               | `hsid-xsim.sh -w hsid_main`             |
| [`hsid_x_registers`](../design/hsid_x_registers.md) | `hsid-xsim.sh -w hsid_x_registers`      |
| [`hsid_x_obi_mem`](../design/hsid_x_obi_mem.md)     | `hsid-xsim.sh -w hsid_x_obi_mem`        |
| [`hsid_x_top`](../design/hsid_x_top.md)             | `hsid-xsim.sh -w hsid_x_top`            |

### Simulation with `vsim` and QuestaSim

To start a simulation using `vsim`, run the command shown in the listing below. The
terminal output will display informational messages and any errors that may
occur. To run the *testbench* of a different module, simply pass the module code
as a parameter.

```bash
fusesoc run --target sim --tool modelsim hsid_x_top
```

A Bash *script* is also provided to simplify execution and debugging through the
graphical interface of QuestaSim.  This script is located in the project’s `bin`
directory, and its execution options are shown in the listing below. As with FuseSoC,
the *testbench* of any module can be executed by passing it as an argument.

```bash
bin/hsid-vsim.sh [OPTIONS] MODULE_NAME [-- FUSESOC_ARGS...]

# Examples
bin/hsid-vsim.sh hsid_x_top      # Only simulation
bin/hsid-vsim.sh -g hsid_x_top   # Open QuestaSim
bin/hsid-vsim.sh -h              # Show help
```

In addition, FuseSoC integrates a custom `tcl` script for each module, located
in the `hw/tcl/modelsim-do` directory. For example, the script corresponding to
the `hsid_x_top` module is shown in the listing below.

```tcl
# Set variables
set top "hsid_x_top_tb"
set top_opt "${top}_opt"

# Set up visibility into the design for debugging purposes (+acc)
# Set up coverage options (+cover) (collect branch, condition, 
# expression statement, extended toggle, and 
# finite state machine coverage statistics)
vopt +acc +cover=bcesxf $top -o $top_opt

# Add Assertion, Endpoint, and ImmediateAssert to WildcardFilter
set WildcardFilter "Variable Constant Generic Parameter SpecParam \ 
Memory Assertion Endpoint CellInternal ImmediateAssert"

# Add ignore files for coverage if it's necessary

vsim -assertdebug -coverage -cvgperinstance +nowarnTFMPC $top_opt -msgmode both
# add wave -group "Top" /$top/*
add wave -group "Top DUT" /$top/dut/*
add wave -group "Top FSM" /$top/dut/fsm/*
add wave -group "OBI Memory" /$top/dut/obi_mem/*
add wave -group "Main" /$top/dut/main/*
add wave -group "Main FSM" /$top/dut/main/fsm/*
add wave -group "MSE" /$top/dut/main/mse/*
add wave -group "SqDfAcc 1" /$top/dut/main/mse/channel_1/*
add wave -group "SqDfAcc 2" /$top/dut/main/mse/channel_2/*
add wave -group "MSE Comp" /$top/dut/main/mse_comp/*
add wave -group "FIFO Cap" /$top/dut/main/fifo_captured/*
add wave -group "FIFO Ref" /$top/dut/main/fifo_ref/*

view cover
view assertion
```

Once the graphical interface is open, the `tcl` commands shown in the listing
below can be entered into the `Transcript` window. These commands execute the
`tcl` script imported during the FuseSoC setup.

```tcl
do edalize_main.tcl
run -all
```

Within the QuestaSim interface, you can visualize the status of SVA assertions,
code and `covergroup` coverage,signal waveforms, and other debugging information
supported by QuestaSim.

The following table is a summary to simulate all the modules:

| Module                                              | Simulation with `vsim`          | Debug with `QuestaSim`             |
| --------------------------------------------------- | ------------------------------- | ---------------------------------- |
| [`hsid_fifo`](../design/hsid_fifo.md)               | `hsid-vsim.sh hsid_fifo`        | `hsid-vsim.sh -g hsid_fifo`        |
| [`hsid_sq_df_acc`](../design/hsid_sq_df_acc.md)     | `hsid-vsim.sh hsid_sq_df_acc`   | `hsid-vsim.sh -g hsid_sq_df_acc`   |
| [`hsid_divisor`](../design/hsid_divider.md)         | `hsid-vsim.sh hsid_divisor`     | `hsid-vsim.sh -g hsid_divisor`     |
| [`hsid_mse`](../design/hsid_mse.md)                 | `hsid-vsim.sh hsid_mse`         | `hsid-vsim.sh -g hsid_mse`         |
| [`hsid_mse_comp`](../design/hsid_mse_comp.md)       | `hsid-vsim.sh hsid_mse_comp`    | `hsid-vsim.sh -g hsid_mse_comp`    |
| [`hsid_main`](../design/hsid_main.md)               | `hsid-vsim.sh hsid_main`        | `hsid-vsim.sh -g hsid_main`        |
| [`hsid_x_registers`](../design/hsid_x_registers.md) | `hsid-vsim.sh hsid_x_registers` | `hsid-vsim.sh -g hsid_x_registers` |
| [`hsid_x_obi_mem`](../design/hsid_x_obi_mem.md)     | `hsid-vsim.sh hsid_x_obi_mem`   | `hsid-vsim.sh -g hsid_x_obi_mem`   |
| [`hsid_x_top`](../design/hsid_x_top.md)             | `hsid-vsim.sh hsid_x_top`       | `hsid-vsim.sh -g hsid_x_top`       |

!!! note 

    Keep in mind that before debugging with QuestaSim gui, you must execute
    the simulation setup with FuseSoC. If you want to debug `hsid_main`, you must execute `hsid-vsim.sh hsid_main` and then `hsid-vsim.sh -g hsid_main`. The parameter `-g` will open the QuestaSim created by FuseSoC.