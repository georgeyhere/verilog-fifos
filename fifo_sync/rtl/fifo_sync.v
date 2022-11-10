// fifo_sync.v
//
// Simple shared-clocks FIFO.
// Features registered status outputs. 
// 1 clock cycle read and write latency.
// 
//
module fifo_sync #(
    parameter DATA_WIDTH         = 32,
    parameter ADDR_WIDTH         = 10
    )
    (
    input  wire                  i_clk,
    input  wire                  i_rstn,

    // Write Interface
    input  wire [DATA_WIDTH-1:0] i_data,
    input  wire                  i_wr,

    // Read Interface
    output wire [DATA_WIDTH-1:0] o_data,
    input  wire                  i_rd,

    // Status 
    output reg  [ADDR_WIDTH:0]   o_fill,
    output reg                   o_full,
    output reg                   o_empty,
    output reg                   o_almost_empty,
    output reg                   o_almost_full
    );

    localparam FIFO_DEPTH = 2**ADDR_WIDTH;

    // FIFO memory
    reg [DATA_WIDTH-1:0] mem [0:FIFO_DEPTH-1];

    // Wr/Rd pointers
    reg [ADDR_WIDTH-1:0] rptr;
    reg [ADDR_WIDTH-1:0] wptr;

    // lookahead pointers for registered flag gen
    wire [ADDR_WIDTH-1:0] rptr_next;  // one cycle lookahead; for empty flag gen
    wire [ADDR_WIDTH-1:0] rptr_next2; // two cycle lookahead; for almost-empty flag gen

    wire [ADDR_WIDTH-1:0] wptr_next2; // two cycle lookahead; for full flag gen
    wire [ADDR_WIDTH-1:0] wptr_next3; // 3 cycle lookahead; for almost-full flag gen

    // Create BRAM 
    always@(posedge i_clk) begin 
        if(i_wr) mem[wptr] <= i_data;
    end 
    assign o_data = mem[rptr];

    // Lookahead Pointers
    assign rptr_next  = rptr + 'd1;
    assign rptr_next2 = rptr + 'd2;
    assign wptr_next2 = wptr + 'd2;
    assign wptr_next3 = wptr + 'd3;

    initial begin 
        wptr    = 0;
        rptr    = 0;
        o_fill  = 0;
        o_full  = 0;
        o_empty = 1;
        o_almost_empty = 1;
        o_almost_full  = 0;
    end 
    
    always@(posedge i_clk, negedge i_rstn) begin 
        if(!i_rstn) begin 
            wptr    <= 0;
            rptr    <= 0;
            o_fill  <= 0;
            o_full  <= 0;
            o_empty <= 1;
            o_almost_empty <= 1;
            o_almost_full  <= 0;
        end 
        else begin 
            if(i_wr) begin 
                wptr <= wptr + 1;
            end 

            if(i_rd && (rptr != wptr)) begin 
                rptr <= rptr + 1;
            end 

            if(i_wr && !i_rd) o_fill <= (o_fill == FIFO_DEPTH) ? o_fill : o_fill + 1;
            if(!i_wr && i_rd) o_fill <= (o_fill == 0) ? 0 : o_fill - 1;

            casez({i_wr, i_rd, o_full, o_empty})
                // Read but no write; FIFO not empty
                4'b01?0: begin 
                    o_full  <= 0;
                    o_empty <= (rptr_next == wptr);
                    o_almost_empty <= (rptr_next2 == wptr);
                end 

                // Write but no read; FIFO not full
                4'b100?: begin 
                    o_full  <= (wptr_next2 == rptr);
                    o_empty <= 0;
                    o_almost_full <= (wptr_next3 == wptr);
                end 

                // Simultaneous Read and Write; FIFO not empty
                4'b11?0: begin 
                    o_full  <= o_full;  
                    o_empty <= 0;
                end 

                // Simultaneous Read and Write; FIFO is empty
                4'b11?1: begin 
                    o_full  <= 0;
                    o_empty <= 0;
                end 

                default: begin end 
            endcase 
        end 
    end 


`ifdef FORMAL

// Set up f_past registers
    reg f_past_valid_gbl, f_past_valid;
    initial begin 
        f_past_valid     = 0;
        f_past_valid_gbl = 0;
    end 
    always@($global_clock) f_past_valid_gbl <= 1;
    always@(posedge i_clk) f_past_valid     <= 1;

    always@* 
        if(!f_past_valid_gbl) 
            assert(!f_past_valid);

// Set up clocks
    localparam F_CLKBITS = 5;
    wire [F_CLKBITS-1:0] f_clk_step;
    reg  [F_CLKBITS-1:0] f_clk_count;

    assign f_clk_step = $anyconst;

    always@* begin 
        assume(f_clk_step != 0);
        assume(i_clk == f_clk_count[F_CLKBITS-1]);
    end 

    always@($global_clock) begin 
        f_clk_count <= f_clk_count + f_clk_step;
    end 

// Set up resets w/ async assertion 
    always@($global_clock) begin 
        assume($fell(i_rstn) == $fell(i_rstn));

        if(!$rose(i_clk)) assume(!$rose(i_rstn));
    end 

// Set up synchronous inputs
    always@($global_clock) begin 
        if(f_past_valid_gbl) begin 
            if(!$rose(i_clk)) begin 
                assume($stable(i_wr));
                assume($stable(i_data));
                assume($stable(i_rd));

                assert($stable(o_full)  || (!i_rstn));
                assert($stable(o_fill)  || (!i_rstn));
                assert($stable(o_data)  || (o_empty));
            end 
        end 
    end 

// Assert reset state
    always@($global_clock) begin 
        if((!f_past_valid) || (!i_rstn)) begin 
            assume(i_rd == 0);
            assume(i_wr == 0);

            assert(rptr == 0);
            assert(wptr == 0);
            assert(rptr_next  == 1);
            assert(wptr_next2 == 2);
            
            assert(o_fill == 0);
            assert(o_empty);
            assert(!o_full);
        end 
    end 

// Check FIFO fill level
    wire [ADDR_WIDTH:0] f_fill;
    assign f_fill = (wptr>rptr) ? wptr-rptr : rptr-wptr;
    
    initial assert(f_fill == 0);

    always@($global_clock) begin  
        assert(f_fill <= {1'b1, {(ADDR_WIDTH) {1'b0}} });

        if(f_fill == {1'b1, {(ADDR_WIDTH) {1'b0}} })
            assert(o_full);

        if(f_fill == 0)
            assert(o_empty);
    end 

    always@* begin 
        assert((rptr == wptr) == (f_fill == 0));
    end 

// FIFO Contract
// Given any two subsequent values written, the same two values must be read out sometime
// later in the same order.
    (* anyconst *) wire [ADDR_WIDTH:0]   f_const_addr;
    (* anyconst *) reg  [DATA_WIDTH-1:0] f_const_first, f_const_next;

    wire [ADDR_WIDTH:0] f_const_next_addr;
    reg                 f_addr_valid, f_next_valid;
    reg                 f_first_in_fifo, f_second_in_fifo, f_both_in_fifo;
    reg                 f_wait_for_first_read, f_wait_for_second_read;
    reg                 f_read_first, f_read_second; 
    
    assign f_const_next_addr = f_const_addr + 1;

    always@* begin 
        f_addr_valid = 1'b0;

        if((wptr > rptr) && (wptr > f_const_addr) && (rptr <= f_const_addr))
            f_addr_valid = 1'b1;

        else if((wptr < rptr) && (f_const_addr < wptr))
            f_addr_valid = 1'b1;

        else if((wptr < rptr) && (rptr <= f_const_addr)) 
            f_addr_valid = 1'b1;
    end 

    always@* begin 
        f_next_valid = 1'b0;

        if((wptr > rptr) && (wptr > f_const_next_addr) && (rptr <= f_const_next_addr))
            f_next_valid = 1'b1;

        else if ((wptr < rptr) && (f_const_next_addr < wptr))
            f_next_valid = 1'b1;

        else if ((wptr < rptr) && (rptr <= f_const_next_addr))
            f_next_valid = 1'b1;
    end 

    always@* begin 
        f_first_in_fifo  = (f_addr_valid) && 
                           (mem[f_const_addr[ADDR_WIDTH-1:0]] == f_const_first);

        f_second_in_fifo = (f_next_valid) && 
                           (mem[f_const_next_addr[ADDR_WIDTH-1:0]] == f_const_next);

        f_both_in_fifo   = (f_first_in_fifo) && (f_second_in_fifo);    
    end 

    always@* begin 
        f_wait_for_first_read = (f_both_in_fifo) && 
                                ((!i_rd) || (f_const_addr != rptr) || (o_empty));

        f_read_first = (i_rd) && (o_data == f_const_first) && (!o_empty) && 
                       (rptr == f_const_addr) && (f_both_in_fifo);

        f_wait_for_second_read = (f_second_in_fifo) &&
                                 ((!i_rd) || (o_empty)) &&
                                 (f_const_next_addr == rptr);
        
        f_read_second = (i_rd) && (o_data == f_const_next) && (!o_empty) &&
                        (rptr == f_const_next_addr) &&
                        (f_second_in_fifo);
    end

    always@($global_clock) begin 
        if(f_past_valid_gbl && i_rstn) begin 
            if((!$past(f_read_first)) && (($past(f_both_in_fifo)))) //FIXME:
                assert((f_wait_for_first_read) || (($rose(i_clk))&&(f_read_first)));

            if ($past(f_read_first)) 
                assert(
                    ((!$rose(i_clk))&&(f_read_first)) ||($rose(i_clk)&&((f_read_second) ||
                      (f_wait_for_second_read))));

            if ($past(f_wait_for_second_read))
                assert((f_wait_for_second_read) ||(($rose(i_clk)) && (f_read_second)));
            
        end 
    end

// Cover
    always@(posedge i_clk) begin 
        cover(i_rstn);
        cover(i_wr);
        cover(i_rd);
        cover(o_empty && i_rd);
        cover((o_full) && (i_wr));
    end 

    always@(posedge i_clk) 
        if(f_past_valid) 
            cover($past(o_full) && ($past(i_wr)) && (o_full));

    always@(posedge i_clk) 
        if(f_past_valid) 
            cover($past(o_full) && (!o_full));

    always@($global_clock) begin 
        if(f_past_valid_gbl)
            cover((o_empty) && (!$past(o_empty)));
    end 

    always@* 
        cover(o_full);

`endif 

endmodule
