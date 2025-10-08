# HSpecID-X

This project is a RTL hardware Domain-Specific Accelerator (DSA) to classify hyperspectral pixels (HSPs) using reference signatures from spectral libraries for X-HEEP. 

## Features

- Modular RTL hardware accelerator for hyperspectral pixel classification
- Computes mean squared error (MSE) between pixels and reference spectral signatures
- Designed for integration with X-HEEP (RISC-V, low-power) platforms
- Pipeline and dataflow architecture in SystemVerilog
- Supports embedded/on-board systems with strict resource and power constraints
- Interfaces for X-HEEP platform and spectral library access
- Verification with testbenches, SVA assertions, coverage analysis, and constrained-random stimulus
- Highly parametrizable to adapt to multiples hardware conditions
- Configurable by software through Register Interface of XAIF interface
- Achieves high functional coverage (87% in main module)
- Results validated against golden model in testbenches
- Includes build, simulation, and reporting scripts for developer workflows
- Licensed under CERN-OHL-P v2, with third-party modules under Apache/Solderpad licenses

## Overview

Identifying the composition of the observed material is a common task in any
research laboratory, but this problem becomes more complex when we aim to
explore completely inaccessible places such as asteroids or vast areas of
agricultural land. Thanks to advances in spectroscopy, cameras have been
designed that can capture the light intensity of hundreds of wavelengths per
pixel (HSP), forming a two-dimensional image. These hyperspectral images (HSI)
contain so much information that their computational cost makes processing
difficult in embedded and on-board systems, where resources and power
consumption are very limited.

This project aims at the RTL-level design and verification of a domain-specific
hardware accelerator (DSA) capable of computing the mean squared error between a
hyperspectral pixel and multiple reference signatures stored in a spectral
library, with the goal of identifying he composition of the observed object.
This accelerator includes the interfaces required for integration with the
X-HEEP platform, which is based on RISC-V processors and focused on low-power
applications.

The design has been developed in a modular way in SystemVerilog, using a
pipeline and dataflow architecture. Verification of the design has been carried
out with testbenches, SVA assertions, coverage analysis, and constrained-random
stimulus, achieving 87% coverage in the main module. The results of the
accelerator match the golden model defined in the testbenches, demonstrating its
correct operation and a performance consistent with the expectations defined in
the requirements phase.

## License

This project is licensed under the **CERN-OHL-P v2** (Permissive).  
You are free to use, modify, and distribute this design, provided that the
copyright notice and license text are retained.  

See the [LICENSE](./LICENSE) file for details.  
More information about CERN-OHL-P v2 can be found at the [CERN OHL
website](https://cern-ohl.web.cern.ch/).