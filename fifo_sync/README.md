# fifo_sync


__Description__

This is a basic synchronous FIFO. 
This project was done to practice formal verifiation.


__Testing and Verification__

Verified using SV concurrent assertions and SymbiYosys. 

Assertions check the following:
    - FIFO fill level 
    - Empty flag behavior
    - Full flag behavior
    - Error flag behavior
    - Read/Write pointer behavior 