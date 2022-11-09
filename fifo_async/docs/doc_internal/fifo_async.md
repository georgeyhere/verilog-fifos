# Entity: fifo_async 

- **File**: fifo_async.v
## Diagram

![Diagram](fifo_async.svg "Diagram")
## Description



 This module implements an indepedent clocks FIFO.

 Follows the Gray code counter - Style #2 from the following paper:
 -> http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf

 Formally verified based on:
 -> https://zipcpu.com/blog/2018/07/06/afifo.html

- flags
    - pessimistic
        - flags are removed late
        - two cycle delay due to double FFs
        - note that flags are still set 'accurately'

    - empty flag (read domain)
        - removed with synchronized write pointer

    - full flag  (write domain)
        - removed with synchronized read pointer


## Generics

| Generic name       | Type | Value | Description                 |
| ------------------ | ---- | ----- | --------------------------- |
| DATA_WIDTH         |      | 8     | FIFO data width             |
| PTR_WIDTH          |      | 4     | FIFO greycode pointer width |
| ALMOSTFULL_OFFSET  |      | 1     | Almost Full Flag Offset     |
| ALMOSTEMPTY_OFFSET |      | 1     | Almost Empty Flag Offset    |
## Ports

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
## Signals

| Name                   | Type                  | Description                                     |
| ---------------------- | --------------------- | ----------------------------------------------- |
| mem                    | reg  [DATA_WIDTH-1:0] | FIFO memory                                     |
| raddr                  | wire [PTR_WIDTH-1:0]  | Address pointed to by read pointer (binary)     |
| waddr                  | wire [PTR_WIDTH-1:0]  | Address pointed to by write pointer (binary)    |
| rq1_wptr               | reg  [PTR_WIDTH  :0]  | Read domain write pointer sync stage 1          |
| rq2_wptr               | reg  [PTR_WIDTH  :0]  | Read domain write pointer sync stage 2          |
| rq2_wptr_bin           | wire [PTR_WIDTH  :0]  | Read domain write pointer sync stage 2 (binary) |
| rdiff                  | reg  [PTR_WIDTH  :0]  |                                                 |
| rbin                   | reg  [PTR_WIDTH  :0]  | Binary read pointer w/ rollover detect          |
| rbinnext               | wire [PTR_WIDTH  :0]  | Binary read pointer next state                  |
| rptr                   | reg  [PTR_WIDTH  :0]  | Grey-code read pointer w/ rollover detect       |
| rgraynext              | wire [PTR_WIDTH  :0]  | Grey-code read pointer next state               |
| rempty_val             | wire                  | Read domain empty flag next state               |
| wq1_rptr               | reg  [PTR_WIDTH  :0]  | Write domain read pointer sync stage 1          |
| wq2_rptr               | reg  [PTR_WIDTH  :0]  | Write domain read pointer sync stage 2          |
| wq2_rptr_bin           | wire [PTR_WIDTH  :0]  | Write domain read pointer sync stage 2 (binary) |
| wdiff                  | reg  [PTR_WIDTH  :0]  |                                                 |
| wbin                   | reg  [PTR_WIDTH  :0]  | Binary write pointer w/ rollover detect         |
| wbinnext               | wire [PTR_WIDTH  :0]  | Binary write pointer next state                 |
| wptr                   | reg  [PTR_WIDTH  :0]  | Grey-code write pointer w/ rollover detect      |
| wgraynext              | wire [PTR_WIDTH  :0]  | Grey-code write pointer next state              |
| wfull_val              | wire                  | Write domain full flag next state               |
| f_past_valid_rd        | reg                   |                                                 |
| f_past_valid_wr        | reg                   |                                                 |
| f_past_valid_gbl       | reg                   |                                                 |
| f_wclk_step            | wire [F_CLKBITS-1:0]  |                                                 |
| f_rclk_step            | wire [F_CLKBITS-1:0]  |                                                 |
| f_wclk_count           | reg  [F_CLKBITS-1:0]  |                                                 |
| f_rclk_count           | reg  [F_CLKBITS-1:0]  |                                                 |
| f_fill                 | wire [PTR_WIDTH:0]    |                                                 |
| f_w2r_rbin             | reg  [PTR_WIDTH:0]    |                                                 |
| f_w1r_rbin             | reg  [PTR_WIDTH:0]    |                                                 |
| f_r2w_wbin             | reg  [PTR_WIDTH:0]    |                                                 |
| f_r1w_wbin             | reg  [PTR_WIDTH:0]    |                                                 |
| f_w2r_fill             | wire [PTR_WIDTH:0]    |                                                 |
| f_r2w_fill             | wire [PTR_WIDTH:0]    |                                                 |
| f_const_addr           | wire [PTR_WIDTH:0]    |                                                 |
| f_const_first          | reg  [DATA_WIDTH-1:0] |                                                 |
| f_const_next           | reg  [DATA_WIDTH-1:0] |                                                 |
| f_const_next_addr      | wire [PTR_WIDTH:0]    |                                                 |
| f_addr_valid           | reg                   |                                                 |
| f_next_valid           | reg                   |                                                 |
| f_first_in_fifo        | reg                   |                                                 |
| f_second_in_fifo       | reg                   |                                                 |
| f_both_in_fifo         | reg                   |                                                 |
| f_wait_for_first_read  | reg                   |                                                 |
| f_wait_for_second_read | reg                   |                                                 |
| f_read_first           | reg                   |                                                 |
| f_read_second          | reg                   |                                                 |
## Constants

| Name      | Type | Value | Description |
| --------- | ---- | ----- | ----------- |
| F_CLKBITS |      | 5     |             |
## Processes
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_wclk or negedge i_wrstn) )
  - **Type:** always
- unnamed: ( @(posedge i_rclk or negedge i_rrstn) )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @(posedge i_rclk, negedge i_rrstn) )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @(posedge i_wclk, negedge i_wrstn) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_rclk) )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @(posedge i_wclk or negedge i_wrstn) )
  - **Type:** always
- unnamed: ( @(posedge i_rclk or negedge i_rrstn) )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_rclk) )
  - **Type:** always
- unnamed: ( @($global_clock) )
  - **Type:** always
- unnamed: ( @* )
  - **Type:** always
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_wclk) )
  - **Type:** always
- unnamed: ( @(posedge i_rclk) )
  - **Type:** always
