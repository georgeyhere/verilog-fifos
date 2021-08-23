# verilog-fifos
 Formally verified asynchronous and synchronous FIFO

 # fifo_async

__Description__

This is a basic asynchronous FIFO based on Cliff Cumming's paper on [Simulation and Synthesis Techniques for Asynchonous FIFO Design](http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf). 
This project was done to learn about clock domain crossing techniques as well as practice SystemVerilog and learn about formal verifiation.


In order to avoid multi-bit synchronization issues across clock domains, the read and write pointers use gray-code. Clock domain crossing is handled via double flip-flops.

Note that although the pointers are passed between read and write clock domains in gray-code, they are decoded to binary for more straightforward memory addressing.


The logic for the full flag is handled in the write clock domain. When the full flag is asserted, further writes are ignored.


The logic for the empty flag is handled in the read clock domain. When the empty flag is asserted, FIFO read data is invalid.




__Testing and Verification__

Tested w/ SystemVerilog testbench in Vivado Simulator. Formal using formal properties provided by [ZipCPU](https://zipcpu.com/blog/2018/07/06/afifo.html) in SymbiYosys. 

- fifo_async_tb.sv
    - writes random data into FIFO until full from queue
    - tests read during write
    - tests read until empty

- Assertions check the following:
    - internal values on reset for read/write clock domains
    - FIFO fill level
    - empty and full flag behavior
    - read and write pointer behavior 
    - cdc gray-code counters and registers

The formal contract for fifo_async is relatively straightforward: 

1) Write two consecutive items into the FIFO, starting from
   an arbitrary address.
   These items are stored in a formal-only register.


2) Read the first item from the FIFO and compare against
   the first stored value.


3) Read the second item from the FIFO and compare against
   the second stored value.


# fifo_sync


__Description__

This is a basic synchronous FIFO. 
This project was done to practice formal verifiation.


__Testing and Verification__

Verified using SV concurrent assertions and SymbiYosys. 

- Assertions check the following:
    - FIFO fill level 
    - Empty flag behavior
    - Full flag behavior
    - Error flag behavior
    - Read/Write pointer behavior 
