# Verification

This guide explains the verification flow used in this project. The main entry point is the helper script `bin/hsid-coverage.sh`, which:

- Invokes the FuseSoC `coverage` target for a selected module
- Runs a QuestaSim/ModelSim simulation configured for coverage
- Executes the module-specific TCL script to save coverage and generate reports
- Collects the resulting reports into a single folder for easy browsing

The flow is repeatable per module (e.g., `hsid_divider`, `hsid_main`, …).

## End-to-end workflow

1) Choose a module and run the coverage helper script

```bash
# General form (from repo root)
bin/hsid-coverage.sh MODULE_NAME [-- FUSESOC_ARGS...]

# Examples
bin/hsid-coverage.sh hsid_divider
bin/hsid-coverage.sh hsid_main -- --K=32   # pass parameters through to FuseSoC
bin/hsid-coverage.sh -h                     # show help
```

2) What the script does under the hood

- Calls FuseSoC with the `coverage` target for the selected core, e.g.:
	- `fusesoc run --no-export --target coverage uclm:hspecidx:hsid_main [FUSESOC_ARGS...]`
- The core’s `coverage` target (see `*.core`) configures the ModelSim backend to enable coverage and points to the module’s coverage TCL:
	- `+cover=bcestf` enables block, condition, expression, statement, toggle, and FSM code coverage
	- `-coverage -assertdebug` enables collection of UCDB and assertion data
	- `-do .../hw/tcl/modelsim-do/<module>_coverage.tcl` runs the post-sim reporting
- After the simulation completes, the TCL script saves the UCDB and emits multiple reports.
- Finally, `hsid-coverage.sh` copies the generated reports into a consolidated output folder.

3) Where results are stored

- By default, `hsid-coverage.sh` copies artifacts to:
	- `reports/<MODULE_NAME>/`

## Module–specific TCL and core wiring (example: hsid_main)

- Core file: `hsid_main.core`
	- `targets.coverage.tools.modelsim` sets:
		- `vlog_options: +cover=bcestf +acc`
		- `vsim_options: -onfinish stop -coverage -assertdebug -do ../../../hw/tcl/modelsim-do/hsid_main_coverage.tcl`
	- Top-level for coverage: `hsid_main_tb`

- TCL driver: `hw/tcl/modelsim-do/hsid_main_coverage.tcl`
	- Runs the full test (`run -all`)
	- Saves UCDB: `coverage save -testname $top report/$top.ucdb`
	- Generates reports (text, XML, HTML)
	- Focuses DUT code coverage using instances `/$top/dut` and `/$top/dut/fsm`

The divider module follows the same pattern (see `hsid_divider_coverage.tcl`).

## Generated files and their meaning

The coverage TCL scripts emit the following artifacts (paths shown relative to the working run directory; copies end up under `reports/<MODULE_NAME>/`):

- UCDB database
	- `report/<top>.ucdb` — Unified coverage database containing SVA, CVG, and code coverage.

- Global summary (text)
	- `report/summary.txt` — Coverage summary across assertions, functional coverage, and code coverage.

- Assertions (SVA)
	- `report/sva_details.txt` — Detailed assertion status (concurrent SVA), pass/fail/hit counts.
	- `report/sva_details.xml` — Same as above in XML format for tooling.

- Functional coverage (CVG)
	- `report/cvg_details.txt` — Detailed covergroups/coverpoints/crosses and bin hits.
	- `report/cvg_details.xml` — XML version for tooling.

- Code coverage (by DUT instance)
	- Text: `report/dut_code.txt`
	- XML:  `report/dut_code.xml`
	- Instances:
		- Divider flow: `/$top/dut`
		- Main flow: `/$top/dut` and `/$top/dut/fsm`

- HTML report
	- `report/html/index.html` — Browsable HTML including SVA, CVG, and code coverage views.

## Code coverage categories (bcestf)

The `-code bcestf` option enables:

- b: Block coverage
- c: Condition coverage
- e: Expression coverage
- s: Statement coverage
- t: Toggle coverage
- f: FSM coverage

This combination offers a thorough view of RTL execution and logic activation.

## How to interpret results

- Start with `summary.txt` for a global picture of SVA/CVG/code coverage.
- Drill into `sva_details.txt`/`.xml` to inspect assertion quality.
- Use `cvg_details.txt`/`.xml` to identify unhit bins and coverage holes in your test intent.
- Use `dut_code.txt`/`.xml` and the HTML report to locate uncovered RTL constructs (by block/condition/expression/statement/toggle/FSM) and specific instances (e.g., DUT and FSM submodule).

## Troubleshooting

- If no UCDB is created, ensure the coverage target is used and ModelSim is invoked with `-coverage` and compile with `+cover=bcestf`.
- If reports are empty, check that the test actually runs to completion (`run -all`) and that the TCL is executed (`-do <module>_coverage.tcl`).
- If outputs don’t appear under `reports/<MODULE_NAME>/`, verify that `hsid-coverage.sh` finished successfully; artifacts originate from `build/uclm_hspecidx_<MODULE_NAME>_0/coverage-modelsim/report/`.

