# Divisor (`hsid_divider`) {#hsid_divider}

The divisor included in this project is a blocking module without pipelining.
This operation is performed at the end of the
[`hsid_sq_df_acc`](hsid_sq_df_acc.md) module, after the final accumulator, within
the [`hsid_mse`](hsid_mse.md) module. To ensure correct operation, you must make
sure that **HSP** is large enough to avoid issues with the overall dataflow.

A non-restoring division algorithm for unsigned integers is used to perform the
division, operating over `K` iterations to produce a `K`-bit quotient and
remainder from a `2*K`-bit dividend.

The divider accepts a `2*K`-bit `dividend` and a `K`-bit `divisor`. On `start`,
it initializes an internal remainder register (`rem_reg`) with the most
significant half of the dividend, and a shift register (`q_reg`) with the least
significant half of the dividend. During each cycle, it shifts the remainder
left, brings in the next dividend bit, and then conditionally adds or subtracts
an extended divisor (`divisor_ext`) to compute the next remainder and quotient
bit. After `K` compute cycles, the quotient and final remainder are presented on
the outputs. The figure below shows the combinational logic for the previously
described 8-bit divider. This logic is somewhat complex and must be executed
within a single cycle.

![Combinational logic for `hsid_divider`](../figures/hsid_divider-structure.png){.center width=95%}

In the figure below, you can find its `FSM` with all the states and its
transitions. There is a possibility to cancel out the division and stop all
operations.

![FSM of module `hsid_divider`](../figures/hsid_divider_fsm.png){.center width=75%}

This implementation constains an overflow verification which asserts the input
dividend is too big for the input divisor. There's also be an input overflow to
detect is the input dividend is already overflown. This verification is asserted
before the FSM begins.