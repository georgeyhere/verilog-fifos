// fifo_async.v
//
//! This module implements an indepedent clocks FIFO.
//
//! Follows the Gray code counter - Style #2 from the following paper:
//! -> http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf
//
//! Formally verified based on:
//! -> https://zipcpu.com/blog/2018/07/06/afifo.html
//
//!- flags
//!    - pessimistic
//!        - flags are removed late
//!        - two cycle delay due to double FFs
//!        - note that flags are still set 'accurately'
//
//!    - empty flag (read domain)
//!        - removed with synchronized write pointer
//
//!    - full flag  (write domain)
//!        - removed with synchronized read pointer
//
/*
INSTANTIATION TEMPLATE:

fifo_async #(
    .DATA_WIDTH         (DATA_WIDTH),
    .PTR_WIDTH          (ADDR_WIDTH),
    .ALMOSTFULL_OFFSET  (ALMOSTFULL_OFFSET),
    .ALMOSTEMPTY_OFFSET (ALMOSTEMPTY_OFFSET) 
) 
DUT (
    .i_wclk         (),
    .i_wrstn        (),
    .i_wr           (),
    .i_wdata        (),
    .o_wfill        (),
    .o_wfull        (),
    .o_walmostfull  (),
    
    .i_rclk         (),
    .i_rrstn        (),
    .i_rd           (),
    .o_rdata        (),
    .o_rfill        (),
    .o_rempty       (),
    .o_ralmostempty ()
);
*/
module fifo_async 
    #(parameter DATA_WIDTH         = 8, //! FIFO data width
      parameter PTR_WIDTH          = 4, //! FIFO greycode pointer width
      parameter ALMOSTFULL_OFFSET  = 1, //! Almost Full Flag Offset
      parameter ALMOSTEMPTY_OFFSET = 1) //! Almost Empty Flag Offset
    (
    // WRITE INTERFACE
    input  wire                  i_wclk,         //! Write Clock
    input  wire                  i_wrstn,        //! Async active-low Write Reset
    input  wire                  i_wr,           //! Write Enable
    input  wire [DATA_WIDTH-1:0] i_wdata,        //! Write Data In
    output reg                   o_wfull,        //! Write Full Flag
    output reg                   o_walmostfull,  //! Write Almost Full Flag
    output reg  [PTR_WIDTH   :0] o_wfill,        //! Write Fill Level

    // READ INTERFACE
    input  wire                  i_rclk,         //! Read Clock
    input  wire                  i_rrstn,        //! Async active-low Read Reset
    input  wire                  i_rd,           //! Read Enable
    output wire [DATA_WIDTH-1:0] o_rdata,        //! Read Data In
    output reg                   o_rempty,       //! Read Empty Flag
    output reg                   o_ralmostempty, //! Read Almost Empty Flag
    output reg  [PTR_WIDTH   :0] o_rfill         //! Read Fill Level
    );

// FIFO MEMORY
    reg  [DATA_WIDTH-1:0] mem [0:((1<<PTR_WIDTH)-1)]; //! FIFO memory
    wire [PTR_WIDTH-1:0] raddr;        //! Address pointed to by read pointer (binary)
    wire [PTR_WIDTH-1:0] waddr;        //! Address pointed to by write pointer (binary)
 
// READ LOGIC
    reg  [PTR_WIDTH  :0] rq1_wptr;     //! Read domain write pointer sync stage 1
    reg  [PTR_WIDTH  :0] rq2_wptr;     //! Read domain write pointer sync stage 2
    wire [PTR_WIDTH  :0] rq2_wptr_bin; //! Read domain write pointer sync stage 2 (binary)
    reg  [PTR_WIDTH  :0] rdiff;
 
    reg  [PTR_WIDTH  :0] rbin;         //! Binary read pointer w/ rollover detect
    wire [PTR_WIDTH  :0] rbinnext;     //! Binary read pointer next state 
  
    reg  [PTR_WIDTH  :0] rptr;         //! Grey-code read pointer w/ rollover detect
    wire [PTR_WIDTH  :0] rgraynext;    //! Grey-code read pointer next state
    wire                 rempty_val;   //! Read domain empty flag next state 

// WRITE LOGIC
    reg  [PTR_WIDTH  :0] wq1_rptr;     //! Write domain read pointer sync stage 1
    reg  [PTR_WIDTH  :0] wq2_rptr;     //! Write domain read pointer sync stage 2
    wire [PTR_WIDTH  :0] wq2_rptr_bin; //! Write domain read pointer sync stage 2 (binary)
    reg  [PTR_WIDTH  :0] wdiff; 

    reg  [PTR_WIDTH  :0] wbin;         //! Binary write pointer w/ rollover detect
    wire [PTR_WIDTH  :0] wbinnext;     //! Binary write pointer next state
   
    reg  [PTR_WIDTH  :0] wptr;         //! Grey-code write pointer w/ rollover detect
    wire [PTR_WIDTH  :0] wgraynext;    //! Grey-code write pointer next state
    wire wfull_val;                    //! Write domain full flag next state
 
// INITIAL VALUES
    initial begin
        rbin = 0;
        rptr = 0;
        o_rempty = 1;

        wbin = 0;
        wptr = 0;
        o_wfull = 0;

        {rq1_wptr, rq2_wptr} = 0;
        {wq1_rptr, wq2_rptr} = 0;
    end

// FIFO MEMORY
    assign o_rdata = mem[raddr];
    always@(posedge i_wclk) begin
        if((i_wr) && (!o_wfull)) mem[waddr] <= i_wdata;
    end

// POINTER CDC
    always@(posedge i_wclk or negedge i_wrstn) begin
        if(!i_wrstn) {wq2_rptr, wq1_rptr} <= 0;
        else         {wq2_rptr, wq1_rptr} <= {wq1_rptr, rptr};
    end

    always@(posedge i_rclk or negedge i_rrstn) begin
        if(!i_rrstn) {rq2_wptr, rq1_wptr} <= 0;
        else         {rq2_wptr, rq1_wptr} <= {rq1_wptr, wptr};
    end

// READ LOGIC + EMPTY GENERATION
    assign raddr      = rbin[PTR_WIDTH-1:0];
    assign rbinnext   = rbin + { {(PTR_WIDTH){1'b0}}, ((i_rd) && (!o_rempty)) };
    assign rgraynext  = (rbinnext >> 1) ^ rbinnext;
    assign rempty_val = (rgraynext == rq2_wptr);
    
    assign rq2_wptr_bin[PTR_WIDTH] = rq2_wptr[PTR_WIDTH];
    genvar i;
    for(i=PTR_WIDTH-1; i>=0; i=i-1) begin
        xor(rq2_wptr_bin[i], rq2_wptr[i], rq2_wptr_bin[i+1]);
    end

    always@* begin 
        if(rbinnext <= rq2_wptr_bin) 
            rdiff = rq2_wptr_bin - rbinnext; 
        else 
            rdiff = (1<<(PTR_WIDTH+1)) - rbinnext + rq2_wptr_bin;
    end 

    always@(posedge i_rclk, negedge i_rrstn) begin 
        if(!i_rrstn) begin 
            rbin           <= 0;
            rptr           <= 0;
            o_rfill        <= 0;
            o_rempty       <= 1;
            o_ralmostempty <= 1;
        end 
        else begin 
            rbin           <= rbinnext;
            rptr           <= rgraynext;
            o_rfill        <= rdiff;
            o_rempty       <= rempty_val; 
            o_ralmostempty <= (rdiff <= ALMOSTEMPTY_OFFSET);
        end 
    end 

// WRITE LOGIC + FULL GENERATION
    assign waddr     = wbin[PTR_WIDTH-1:0];
    assign wbinnext  = wbin + { {(PTR_WIDTH){1'b0}}, ((i_wr) && (!o_wfull)) };
    assign wgraynext = (wbinnext >> 1) ^ wbinnext; 
    assign wfull_val = (wgraynext == {~wq2_rptr[PTR_WIDTH:PTR_WIDTH-1], wq2_rptr[PTR_WIDTH-2:0]});
              
    assign wq2_rptr_bin[PTR_WIDTH] = wq2_rptr[PTR_WIDTH];
    genvar j;
    for(j=PTR_WIDTH-1; j>=0; j=j-1) begin
        xor(wq2_rptr_bin[j], wq2_rptr[j], wq2_rptr_bin[j+1]);
    end

    always@* begin 
        if(wq2_rptr_bin <= wbinnext)
            wdiff = (wbinnext - wq2_rptr_bin);
        else 
            wdiff = ((1<<(PTR_WIDTH+1)) - wq2_rptr_bin + wbinnext); 
    end     
                   
    always@(posedge i_wclk, negedge i_wrstn) begin 
        if(!i_wrstn) begin 
            wbin          <= 0;
            wptr          <= 0;
            o_wfill       <= 0;
            o_wfull       <= 0;
            o_walmostfull <= 0;
        end 
        else begin 
            wbin          <= wbinnext;
            wptr          <= wgraynext;
            o_wfull       <= wfull_val;
            o_wfill       <= wdiff;
            o_walmostfull <= (o_wfill >= ( ((1<<PTR_WIDTH)-ALMOSTFULL_OFFSET)) ) ||
                             (wgraynext == {~wq2_rptr[PTR_WIDTH:PTR_WIDTH-1], wq2_rptr[PTR_WIDTH-2:0]});
        end 
    end 


`ifdef FORMAL

// Set up f_past_valid registers
    reg f_past_valid_rd, f_past_valid_wr, f_past_valid_gbl;
    initial begin 
        f_past_valid_rd = 0;
        f_past_valid_wr = 0;
        f_past_valid_gbl = 0;
    end 

    always@($global_clock)  f_past_valid_gbl <= 1;
    always@(posedge i_wclk) f_past_valid_wr  <= 1;
    always@(posedge i_rclk) f_past_valid_rd  <= 1;

    always@* 
        if(!f_past_valid_gbl) 
            assert((!f_past_valid_wr) && (!f_past_valid_rd));

// Set up read and write clocks
    localparam F_CLKBITS = 5;

    wire [F_CLKBITS-1:0] f_wclk_step, f_rclk_step;
    reg  [F_CLKBITS-1:0] f_wclk_count, f_rclk_count;

    assign f_wclk_step = $anyconst;
    assign f_rclk_step = $anyconst;
    
    always@* begin 
        assume(f_wclk_step != 0);
        assume(f_rclk_step != 0);
        
        assume(i_wclk == f_wclk_count[F_CLKBITS-1]);
        assume(i_rclk == f_wclk_count[F_CLKBITS-1]);
    end 

    always@($global_clock) begin 
        f_wclk_count <= f_wclk_count + f_wclk_step;
        f_rclk_count <= f_rclk_count + f_rclk_step;
    end 

// Set up resets w/ async assertion and sync de-assertion
    initial assume(i_rrstn == i_wrstn);

    always@($global_clock) begin 
        assume($fell(i_wrstn) == $fell(i_rrstn));

        if(!$rose(i_wclk)) assume(!$rose(i_wrstn));
        if(!$rose(i_rclk)) assume(!$rose(i_rrstn));
    end 

    always@($global_clock) 
        if(!i_wrstn) assert(rbin == 0);

// Set up synchronous inputs
    always@($global_clock) begin 
        if(f_past_valid_gbl) begin 

            if(!$rose(i_wclk)) begin 
                assume($stable(i_wr));
                assume($stable(i_wdata));

                assert($stable(o_wfull) || (!i_wrstn));
            end 

            if(!$rose(i_rclk)) begin 
                assume($stable(i_rd));

                assert((o_rempty) || ($stable(o_rdata)));
                assert((!i_rrstn) || ($stable(o_rempty)));
            end 
        end 
    end 

// Assert reset state
    always@($global_clock) begin 
        if((!f_past_valid_wr) || (!i_wrstn)) begin 
            assume(i_wr == 0);

            assert(wptr == 0);
            assert(wbin == 0);
            assert(!o_wfull);

            assert(wq1_rptr == 0);
            assert(wq2_rptr == 0);
            assert(rq1_wptr == 0);
            assert(rq2_wptr == 0);

            assert(rbin == 0);
            assert(o_rempty);
        end 
    end 

    always@($global_clock) begin 
        if((!f_past_valid_rd) || (!i_rrstn)) begin 
            assume(i_rd == 0);

            assert(rptr == 0);
            assert(rbin == 0);
            assert(rq1_wptr == 0);
            assert(rq2_wptr == 0);
            assert(wq1_rptr == 0);
            assert(wq2_rptr == 0);
        end 
    end 

// Calculate FIFO fill level
    wire [PTR_WIDTH:0] f_fill;
    assign f_fill = (wbin - rbin);

    initial assert(f_fill == 0);
    
    always@($global_clock) begin 
        assert(f_fill <= {1'b1, {(PTR_WIDTH) {1'b0}} });

        if(f_fill == {1'b1, {(PTR_WIDTH) {1'b0} }})
            assert(o_wfull);

        if(f_fill == {1'b0, {(PTR_WIDTH){1'b1}}})
            assert((wfull_val) || (!i_wr) || (o_wfull));

        if(f_fill == 0)
            assert(o_rempty);

        if(f_fill == 1) 
            assert((rempty_val) || (!i_rd) || (o_rempty));
    end 

    always@* begin 
        assert(wptr == ((wbin>>1) ^ wbin));
        assert(rptr == ((rbin>>1) ^ rbin));

        assert( (rptr == { ~wptr[PTR_WIDTH:PTR_WIDTH-1], wptr[PTR_WIDTH-2:0]}) ==
                (f_fill == {1'b1, {(PTR_WIDTH){1'b0}} }) );

        assert((rptr == wptr) == (f_fill == 0));
    end 

//
    reg  [PTR_WIDTH:0] f_w2r_rbin, f_w1r_rbin,
                       f_r2w_wbin, f_r1w_wbin;
    wire [PTR_WIDTH:0] f_w2r_fill, f_r2w_fill;

    initial begin 
        {f_w2r_rbin, f_w1r_rbin} = 0;
        {f_r2w_wbin, f_r1w_wbin} = 0;
    end

    assign f_w2r_fill = wbin - f_w2r_rbin;
    assign f_r2w_fill = f_r2w_wbin - rbin;

    always@(posedge i_wclk or negedge i_wrstn) begin 
        if(!i_wrstn) 
            {f_w2r_rbin, f_w1r_rbin} <= 0;
        else 
            {f_w2r_rbin, f_w1r_rbin} <= {f_w1r_rbin, rbin};
    end 

    always@(posedge i_rclk or negedge i_rrstn) begin 
        if(!i_rrstn) 
            {f_r2w_wbin, f_r1w_wbin} <= 0;
        else 
            {f_r2w_wbin, f_r1w_wbin} <= {f_r1w_wbin, wbin};
    end 

    always@* begin   
        assert(rq1_wptr == ((f_r1w_wbin>>1) ^ f_r1w_wbin));
        assert(rq2_wptr == ((f_r2w_wbin>>1) ^ f_r2w_wbin));

        assert(wq1_rptr == ((f_w1r_rbin>>1) ^ f_w1r_rbin));
        assert(wq2_rptr == ((f_w2r_rbin>>1) ^ f_w2r_rbin));

        assert(f_w2r_fill <= { 1'b1, {(PTR_WIDTH){1'b0}} });
        assert(f_r2w_fill <= { 1'b1, {(PTR_WIDTH){1'b0}} });
    end 

    always@*
        if (wptr == { ~wq2_rptr[PTR_WIDTH:PTR_WIDTH-1], wq2_rptr[PTR_WIDTH-2:0] })
		    assert(o_wfull);

    always@*
        if(rptr == rq2_wptr) assert(o_rempty);
     

// Check gray code 
    genvar k;
    generate for(k=0; k<=PTR_WIDTH; k=k+1) begin : CHECK_ONEHOT_WPTR
        always@* 
            assert((wptr[k] == wgraynext[k]) ||
                    (wptr ^ wgraynext ^ (1<<k) == 0));
        
        always@*
            assert((rq2_wptr[k] == rq1_wptr[k])
                ||(rq2_wptr ^ rq1_wptr ^ (1<<k) == 0));
     
    end endgenerate

    genvar k;
    generate for(k=0; k<= PTR_WIDTH; k=k+1) begin : CHECK_ONEHOT_RPTR
        always@* begin 
            assert((rptr[k] == rgraynext[k]) || 
                   (rptr ^ rgraynext ^ (1<<k) == 0));

            assert((wq2_rptr[k] == wq1_rptr[k]) || 
                   (wq2_rptr ^ wq1_rptr ^ (1<<k) == 0));
        end 
    end endgenerate

// FIFO Contract
// Given any two subsequent values written, the same two values must be read out sometime
// later in the same order.
    (* anyconst *) wire [PTR_WIDTH:0]    f_const_addr;
    (* anyconst *) reg  [DATA_WIDTH-1:0] f_const_first, f_const_next;

    wire [PTR_WIDTH:0] f_const_next_addr;
    reg                f_addr_valid, f_next_valid;
    reg                f_first_in_fifo, f_second_in_fifo, f_both_in_fifo;
    reg                f_wait_for_first_read, f_wait_for_second_read;
    reg                f_read_first, f_read_second;

    assign f_const_next_addr = f_const_addr + 1;

    always@* begin 
        f_addr_valid = 1'b0;

        if((wbin > rbin) && (wbin > f_const_addr) && (rbin <= f_const_addr))
            f_addr_valid = 1'b1;
        else if((wbin < rbin) && (f_const_addr < wbin)) 
            f_addr_valid = 1'b1;
        else if((wbin < rbin) && (rbin <= f_const_addr))
            f_addr_valid = 1'b1;
    end 

    always@* begin 
        f_next_valid = 1'b0;

        if((wbin > rbin) && (wbin > f_const_next_addr) && (rbin <= f_const_next_addr))
            f_next_valid = 1'b1;
        else if((wbin < rbin) && (f_const_next_addr < wbin)) 
            f_next_valid = 1'b1;
        else if((wbin < rbin) && (rbin <= f_const_next_addr))
            f_next_valid = 1'b1;
    end 

    always@* begin 
        f_first_in_fifo  = (f_addr_valid) && 
                           (mem[f_const_addr[PTR_WIDTH-1:0]] == f_const_first);

        f_second_in_fifo = (f_next_valid) && 
                           (mem[f_const_next_addr[PTR_WIDTH-1:0]] == f_const_next);

        f_both_in_fifo   = (f_first_in_fifo) && (f_second_in_fifo);
    end 

    always@* begin 
        f_wait_for_first_read = (f_both_in_fifo) && 
                                ((!i_rd) || (f_const_addr != rbin) || (o_rempty));

        f_read_first = (i_rd) && (o_rdata == f_const_first) && (!o_rempty) && 
                       (rbin == f_const_addr) && (f_both_in_fifo);

        f_wait_for_second_read = (f_second_in_fifo) &&
                                 ((!i_rd) || (o_rempty)) &&
                                 (f_const_next_addr == rbin);
        
        f_read_second = (i_rd) && (o_rdata == f_const_next) && (!o_rempty) &&
                        (rbin == f_const_next_addr) &&
                        (f_second_in_fifo);
    end 

    always@($global_clock) begin 
        if(f_past_valid_gbl && i_wrstn) begin 
            if((!$past(f_read_first)) && (($past(f_both_in_fifo)))) 
                assert((f_wait_for_first_read) || (($rose(i_rclk))&&(f_read_first)));

            if ($past(f_read_first))
                assert(
                    ((!$rose(i_rclk))&&(f_read_first)) ||($rose(i_rclk)&&((f_read_second) ||
                      (f_wait_for_second_read))));

            if ($past(f_wait_for_second_read))
                assert((f_wait_for_second_read) ||(($rose(i_rclk)) && (f_read_second)));
            
        end 
    end 

// Cover
    always@(posedge i_wclk) 
        cover(i_wrstn);

    always@(posedge i_rclk) 
        cover (i_rrstn);

    always@($global_clock) 
        if(f_past_valid_gbl)
            cover((o_rempty) && (!$past(o_rempty)));

    always@* 
        cover(o_wfull);

    always@(posedge i_wclk) 
        if(f_past_valid_wr) 
            cover($past(o_wfull) && ($past(i_wr)) && (o_wfull));

    always@(posedge i_wclk) 
        if(f_past_valid_wr) 
            cover($past(o_wfull) && (!o_wfull));

    always@(posedge i_wclk) 
        cover((o_wfull) && (i_wr));

    always@(posedge i_wclk)
        cover(i_wr);

    always@(posedge i_rclk)
        cover(o_rempty && i_rd);

`endif

endmodule
