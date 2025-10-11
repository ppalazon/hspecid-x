# HSpecID-X: A Hyperspectral Pixel Classifier Accelerator for X-HEEP 

[![Documentation Status](https://readthedocs.org/projects/hspecid-x/badge/?version=latest)](https://hspecid-x.readthedocs.io/en/latest/)
[![License: CERN-OHL-P v2](https://img.shields.io/badge/License-CERN--OHL--P--v2-blue.svg)](https://ohwr.org/cern_ohl_p_v2.txt)

<figure>
  <img src="https://raw.githubusercontent.com/ppalazon/hspecid-x/main/docs/figures/hspecid-x.png" alt="HSpecID-X logo" width="50%">
</figure>

The main objective of this project is the design at the **RTL** level and the
functional verification of a **domain-specific accelerator (DSA)** for the
classification of **hyperspectral pixels (HSPs)** based on reference signatures
contained in spectral libraries. 

This accelerator will be adapted for integration into a **System-on-Chip (SoC)**
based on **X-HEEP**, targeting *on-edge* and *on-board* environments, where
local data processing is critical.

The accelerator performs the computation of the **Mean Squared Error (MSE)**
between the captured HSP and the signatures in the library in order to determine
which spectral signature best matches the captured data.

More specifically, the technical objectives are:

- **Develop** a hardware accelerator in **SystemVerilog** that implements the
  MSE algorithm for HSP processing, using *pipeline* and *dataflow*
  architectures.
- **Integrate** the accelerator into the **X-HEEP** platform, ensuring
  connectivity with its standard interfaces.
- **Evaluate** performance through functional simulation in **Vivado (xsim)**
  and **Siemens QuestaSim (vsim)**, with signal timing analysis (*waveforms*)
  using **GTKWave** and **QuestaSim**, and by determining the number of cycles
  required to process each HSP.
- **Verify and validate** the design through directed and random *testbenches*,
  **SystemVerilog Assertions (SVA)**, and coverage checks.
- **Optimize** the design to maximize configurability at both software and RTL
  levels, promote code reuse, and enable future scalability, as well as
  synthesis on **FPGA** or **ASIC**.
- **Publish** the design as an **open-hardware** project so that the RTL code
  can be reused by other projects through the **FuseSoC** and **Bender** tools.

Full docs are available at:
[hspecid-x.readthedocs.io](https://hspecid-x.readthedocs.io).

## License

This project is licensed under the **CERN-OHL-P v2** (Permissive).  
You are free to use, modify, and distribute this design, provided that the
copyright notice and license text are retained.  

See the [LICENSE](./LICENSE) file for details.  
More information about CERN-OHL-P v2 can be found at the [CERN OHL
website](https://cern-ohl.web.cern.ch/).

## Third-Party Components

- **common_cells** – licensed under [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
- **register_interface** – licensed under [Solderpad Hardware License v0.51](http://solderpad.org/licenses/SHL-0.51/).
- **obi** – [Solderpad Hardware License v0.51](http://solderpad.org/licenses/SHL-0.51/).

Original licenses and attributions are retained in their respective files and headers.