# fifo_async

## Files

__/rtl__  
Verilog source for fifo_async.

__/tb__  
Formal and traditional test solutions with a Makefile to run them.

## Overview
Charts generated via TerosHDL.  

### Parameters

| Parameter name     | Type | Value | Description                 |
| ------------------ | ---- | ----- | --------------------------- |
| DATA_WIDTH         |      | 8     | FIFO data width             |
| PTR_WIDTH          |      | 4     | FIFO greycode pointer width |
| ALMOSTFULL_OFFSET  |      | 1     | Almost Full Flag Offset     |
| ALMOSTEMPTY_OFFSET |      | 1     | Almost Empty Flag Offset    |


### Top-Level Interface

| Port name      | Direction | Type                  | Description                  |
| -------------- | --------- | --------------------- | ---------------------------- |
| i_wclk         | input     | wire                  | Write Clock                  |
| i_wrstn        | input     | wire                  | Async active-low Write Reset |
| i_wr           | input     | wire                  | Write Enable                 |
| i_wdata        | input     | wire [DATA_WIDTH-1:0] | Write Data In                |
| o_wfull        | output    |                       | Write Full Flag              |
| o_walmostfull  | output    |                       | Write Almost Full Flag       |
| o_wfill        | output    | [PTR_WIDTH   :0]      | Write Fill Level             |
| i_rclk         | input     | wire                  | Read Clock                   |
| i_rrstn        | input     | wire                  | Async active-low Read Reset  |
| i_rd           | input     | wire                  | Read Enable                  |
| o_rdata        | output    | wire [DATA_WIDTH-1:0] | Read Data In                 |
| o_rempty       | output    |                       | Read Empty Flag              |
| o_ralmostempty | output    |                       | Read Almost Empty Flag       |
| o_rfill        | output    | [PTR_WIDTH   :0]      | Read Fill Level              |



