# Hardware configuration

This page documents the recommended developer workflow to configure the
accelerator register map via the HJSON file `data/hsid_x_ctrl.hjson`, run the
register-generation script `bin/hsid-ctrl-reg-gen.sh`, and update the
SystemVerilog package `hw/src/hsid_pkg/rtl/hsid_pkg.sv` so internal constants
match the register definitions.

## Goal

- Edit register definitions (fields, widths, addresses) in `data/hsid_x_ctrl.hjson`.
- Run `bin/hsid-ctrl-reg-gen.sh` to regenerate RTL wrappers, C headers and
	Markdown register documentation.
- Update any project-wide SystemVerilog constants (for example, bit-width
	constants in `hsid_pkg.sv`) that depend on register field sizes.

## Prerequisites

- Have a working Python environment and `regtool` available at
	`hw/deps/register_interface/vendor/lowrisc_opentitan/util/regtool.py` (this is
	the path used by the repository script). The script will fail if `regtool`
	is missing.
- Use the project's `direnv` / `.envrc` setup so `PATH` and other environment
	variables are available (recommended). See `README.md` for a template `.envrc`.

## Files of interest

- `data/hsid_x_ctrl.hjson`  — HJSON register description used as the single
	source of truth for registers and fields.
- `bin/hsid-ctrl-reg-gen.sh` — wrapper script that runs `regtool` and places
	generated artifacts under `hw/src/hsid_x_ctrl_reg/rtl`, `sw/` and
	`docs/design/`.
- `hw/src/hsid_pkg/rtl/hsid_pkg.sv` — project SystemVerilog package with
	relevant constants (`HSID_HSP_LIBRARY_WIDTH`, etc.) which must be kept in
	sync with register field widths where appropriate.

## Steps

### Step 1 — Edit the HJSON register description

1. Open `data/hsid_x_ctrl.hjson` in an editor.
2. Modify or add registers/fields. Key examples in the file:

	 - `LIBRARY_SIZE` field currently uses `"bits": "5:0"` (6 bits → max 63).
		 Increase to e.g. `"7:0"` if you need to address up to 255 entries.
	 - `PIXEL_BANDS` uses `"6:0"` (7 bits → max 127 bands).

	 Example change (conceptual):

	 - Before: `"bits": "5:0"` (6 bits)
	 - After : `"bits": "7:0"` (8 bits)

3. Save the `data/hsid_x_ctrl.hjson` file.

#### Notes and pitfalls

- Ensure field bit ranges do not overlap incorrectly within the same register.
- Use the regtool documentation if you want to add multi-field registers or
	complex fields (bitfields, enumerations, reset values, access types).

### Step 2 — Run the register generation script

The project contains a helper script which wraps regtool. Run it from the
project root:

```bash
cd /path/to/hspecid-x
bin/hsid-ctrl-reg-gen.sh
```

What the script does (summary)
- Verifies `regtool` exists at `hw/deps/register_interface/vendor/lowrisc_opentitan/util/regtool.py`.
- Runs regtool to generate Verilog RTL into `hw/src/hsid_x_ctrl_reg/rtl`.
- Generates a software header into `sw/hsid_x_ctrl_reg.h` (script sets `--cdefines`).
- Emits human-readable Markdown documentation into `docs/design/hsid_x_ctrl_reg.md`.

#### Verify generated artifacts

- RTL:  `hw/src/hsid_x_ctrl_reg/rtl/` — contains generated register RTL.
- SW:   `sw/hsid_x_ctrl_reg.h` — C header with register addresses and bitfields.
- Docs: `docs/design/hsid_x_ctrl_reg.md` — auto-generated register docs.

#### If the script fails

- Confirm `REGTOOL` location in the script matches an existing file. If you
	vendor a different `regtool` path, update the script or make a symlink.
- Ensure Python version is compatible with LowRISC regtool (script assumes a
	working interpreter in your environment).

### Step 3 — Update SystemVerilog package constants

Some SystemVerilog constants in `hw/src/hsid_pkg/rtl/hsid_pkg.sv` reflect the
widths used by the register map and other modules. When you change register
field widths (for example, increase `LIBRARY_SIZE` bits), update these
constants to keep the RTL consistent.

Relevant lines in `hsid_pkg.sv` (current values):

```verilog
	localparam int HSID_WORD_WIDTH = 32; // Width of the word in bits
	localparam int HSID_DATA_WIDTH = 16; // 16 bits (but only 14 bits used from hsi pixel)
	localparam int HSID_DATA_WIDTH_MUL = 32; // Data width for multiplication (32 bits)
	localparam int HSID_DATA_WIDTH_ACC = 40; // Data width for accumulator
	localparam int HSID_HSP_BANDS_WIDTH = 7; // Number of bits for Hyperspectral Pixels (7 bits - 127 bands)
	localparam int HSID_HSP_LIBRARY_WIDTH = 6; // Numer of bits for Hyperspectral Pixels Library (6 bits - 64 pixels)
	localparam int HSID_FIFO_ADDR_WIDTH = 2; // Number of bits for buffer address (4 entries)
	localparam int HSID_MEM_ACCESS_WIDTH = HSID_HSP_BANDS_WIDTH + HSID_HSP_LIBRARY_WIDTH; // Number of bits for addressable memory with pixels
```

If you changed `LIBRARY_SIZE` from 6 bits to 8 bits, update `HSID_HSP_LIBRARY_WIDTH` accordingly, for example:

```diff
-  localparam int HSID_HSP_LIBRARY_WIDTH = 6; // 6 bits - 64 pixels
+  localparam int HSID_HSP_LIBRARY_WIDTH = 8; // 8 bits - 256 pixels
```

Then recompute `HSID_MEM_ACCESS_WIDTH` if it uses these constants (the file
already computes it as `HSID_HSP_BANDS_WIDTH + HSID_HSP_LIBRARY_WIDTH`).

#### How to edit safely

- Edit `hw/src/hsid_pkg/rtl/hsid_pkg.sv` with your editor and change the
	numeric localparam(s) to the new width.
- Run a quick repository-wide grep to find uses that might need adjustment:

```bash
git grep HSID_HSP_LIBRARY_WIDTH || true
```

Optional: small `sed` example to patch the constant (run from repo root):

```bash
sed -i "s/HSID_HSP_LIBRARY_WIDTH = 6/HSID_HSP_LIBRARY_WIDTH = 8/" hw/src/hsid_pkg/rtl/hsid_pkg.sv
```

### Step 4 — Rebuild & sanity checks

1. Re-run any lint / simulation flows you normally use (e.g., `bin/hsid-vsim.sh`)
	 to detect mismatches early.
2. If your build system uses FuseSoC or other automatic checks, run that too.

## Notes about register semantics
- The register `swaccess` and `hwaccess` attributes in the HJSON control how
	software and hardware interact; the regtool-generated RTL will implement the
	access semantics. Familiarize yourself with `rw`, `ro`, `rw1s` and related
	access types used in the file.
- Some control bits (e.g., `START`, `CLEAR`) are implemented as one-shot
	triggers (write-one-to-set / clear-on-read behavior). The generated software
	header documents the access type and should be used by firmware.

## Where generated docs land

- The script writes Markdown docs to `docs/design/hsid_x_ctrl_reg.md`. Add a
	link from your main design doc (`docs/design.md`) or `mkdocs.yml` nav if you
	want the generated documentation to appear in site navigation.

## Example quick workflow (summary)

1. Edit `data/hsid_x_ctrl.hjson` to change field widths.
2. Run `bin/hsid-ctrl-reg-gen.sh` from the project root.
3. Edit `hw/src/hsid_pkg/rtl/hsid_pkg.sv` to update any dependent localparams.
4. Run your simulator or tests to validate the change.

If you want, I can also:
- Add a small unit-check script that parses `data/hsid_x_ctrl.hjson` and
	verifies the HJSON field widths are compatible with `hsid_pkg.sv` constants.
- Update `docs/design.md` to link to `docs/hsid_x_ctrl_reg.md` after generation.


