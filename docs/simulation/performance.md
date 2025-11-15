# Performance

In this section, there are some keynotes parameters and explainitions of the
dataflow and the performance of this DSA accelerator. There are few operations
that are performanced in parallel.

In this project, we configured that 2 bands would be merged together in the same
processor word bitwidth. In this case, every cycle we can receive from memory 2
bands simultaneusly. In this section, the module
[`hsid_main`](../design/hsid_main.md) is analysed.

After the `start`:

- Initialization: $1$ cycle
    - It checks that the number of bands ($n$) and the number of the reference
      signatures ($m$) are not zero. 
- Receive captured HSP on FIFO: $\frac{n}{2}$ cycles
    - That is the most optimistic case, so every cycle we receive `2` bands of the
    captured HSP
- Change state: $1$ cycle
- Receive whole spectral library: $\frac{n * m}{2}$ cycles (pipelined)
    - Write FIFO: $1$ cycle
    - Read FIFO: $1$ cycle
        - It reads from captured HSP and reference signature FIFO
    - Two channels of [`hsid_sq_df_acc](../design/hsid_sq_df_acc.md) 
        - Diff : $1$ cycle
        - Multiplication: $1$ cycle[^1]
        - Accumulation: $1$ cycle
    - Once every $\frac{n}{2}$ cycles:
        - Sum: $1$ cycle
        - Division: $33$ cycles ($K + 1$ using $K=32$ bits) (not pipelined)
        - Comparison: $1$ cycle

So to know the number of cycles needed to execute the whole process:

$$t_{\text{hsid}} = \frac{n}{2} + \frac{n * m}{2} + 40$$

!!! note

    You have to keep in mind that the division modules is not pipelined, so the
    number of bands of captured HSP must be greater than $2 * (4 + K + 1) = 72$
    bands to avoid problems with the dataflow.

[^1]: That is possible using DSP units on an FPGA