<figure>
  <img src="figures/hspecid-x.png" alt="HSpecID-X logo" width="50%">
</figure>

Identifying the composition of the observed material is a common task in any
research laboratory, but this problem becomes more complex when we aim to
explore completely inaccessible places such as asteroids or vast areas of
agricultural land. Thanks to advances in spectroscopy, cameras have been
designed that can capture the light intensity of hundreds of wavelengths per
pixel (HSP), forming a two-dimensional image. These hyperspectral images (HSI)
contain so much information that their computational cost makes processing
difficult in embedded and on-board systems, where resources and power
consumption are very limited.

This project aims at the **RTL-level** design and verification of a
**domain-specific hardware accelerator (DSA)** capable of computing the mean
squared error (MSE) between a hyperspectral pixel (HSP) and multiple reference
signatures stored in a spectral library, with the goal of identifying he
composition of the observed object. This accelerator includes the interfaces
required for integration with the X-HEEP platform, which is based on RISC-V
processors and focused on low-power applications.

The design has been developed in a modular way in SystemVerilog, using a
pipeline and dataflow architecture. Verification of the design has been carried
out with testbenches, SVA assertions, coverage analysis, and constrained-random
stimulus, achieving 87% coverage in the main module. The results of the
accelerator match the golden model defined in the testbenches, demonstrating its
correct operation and a performance consistent with the expectations defined in
the requirements phase.

## Main objective

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

## License

This project is licensed under the **CERN-OHL-P v2** (Permissive).  
You are free to use, modify, and distribute this design, provided that the
copyright notice and license text are retained. More information about
CERN-OHL-P v2 can be found at the [CERN OHL
website](https://cern-ohl.web.cern.ch/).