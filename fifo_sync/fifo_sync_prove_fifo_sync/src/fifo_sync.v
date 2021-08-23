`default_nettype none
//
//
// o_status:
// [ADDR_WIDTH+1:2] -> fifo fill
// [1]    -> fifo full
// [0]    -> fifo empty 
//
module fifo_sync
	#(parameter DATA_WIDTH = 8,
      parameter ADDR_WIDTH = 9
	  )
	(
    input  wire                   i_clk,
    input  wire                   i_rstn,
                   
    input  wire                   i_wr,
    input  wire                   i_data,
                  
    input  wire                   i_rd,
    output reg  [DATA_WIDTH-1:0]  o_data,

    output wire [ADDR_WIDTH+1:0]  o_status,
    output wire                   o_error
	);

	localparam FIFO_DEPTH = (1<<ADDR_WIDTH);

	reg  [DATA_WIDTH-1:0] mem [0:FIFO_DEPTH-1];
 
	reg  [ADDR_WIDTH-1:0] fill     = 0;     
	reg                   overrun  = 0;  // set if write to full FIFO
	reg                   underrun = 0; // set if read from empty FIFO
 
	reg  [ADDR_WIDTH-1:0] wptr     = 0;
	wire [ADDR_WIDTH-1:0] wptr_nxt2;              
	reg  [ADDR_WIDTH-1:0] rptr     = 0;
	wire [ADDR_WIDTH-1:0] rptr_nxt;

	reg                   full     = 0;
	reg                   empty    = 0;

// **** o_status and o_error ****
//
	assign o_status = {fill, full, empty};
	assign o_error  = (overrun || underrun);

// **** FIFO write **** 
// 
	always@(posedge i_clk) begin
		if(i_wr)
			mem[wptr] <= i_data;
	end

// **** FIFO read ****
// - one latency read latency
//
	always@(posedge i_clk) begin
		if(i_rd)
			o_data <= mem[rptr];
	end

// **** Write Pointer ****
// - increment on write if not full  
// - increment on write if full BUT there is simultaneous read
//
	always@(posedge i_clk) begin
		if(!i_rstn) begin
			wptr    <= 0;
			overrun <= 0;
		end
		else begin
			if(i_wr) begin
				if(!full || i_rd) begin
					wptr    <= wptr + 1;
					overrun <= 0;
				end
				else begin
					overrun <= 1;
				end
			end
		end
	end


// **** Read Pointer ****
// - increment on read if not empty
//
	always@(posedge i_clk) begin
		if(!i_rstn) begin
			rptr     <= 0;
			underrun <= 0;
		end
		else begin
			if(i_rd) begin
				if(!empty) begin
					rptr     <= rptr + 1;
					underrun <= 0;
				end
				else begin
					underrun <= 1;
				end
			end
		end
	end

// **** Status: Fill ****
//
	// write to not full fifo
	//    -> increment fill
	
	// read from not empty fifo
	//    -> decrement fill
	
	// read+write from empty fifo
	//    -> successful write, failed read; increment fill

	// read+write from not empty fifo
	// all other cases
	//    -> no change to fill

	always@(posedge i_clk) begin
		if(!i_rstn) begin
			fill <= 0;
		end
		else begin
			if(i_wr && !i_rd && !full)       
				fill <= fill + 1;            
			else if(i_rd && !i_wr && !empty) 
				fill <= fill - 1;            
			else if(i_wr && i_rd && empty)   
				fill <= fill + 1;            
            else                             
				fill <= fill;                
		end
	end

// **** Status: full/empty flags ****
// - look ahead; wptr_nxt2 is used to check if next write will cause
//   an overrun
// - look ahead; rptr_nxt is used to check if next read will cause 
//   an underrun
//
	assign wptr_nxt2 = wptr + 2;
	assign rptr_nxt  = rptr + 1;

	always@(posedge i_clk) begin
		if(!i_rstn) begin
			full  <= 0;
			empty <= 1;
		end
		else begin
			if(i_wr && !i_rd && !full) begin // successful write
				full  <= (wptr_nxt2 == rptr);
				empty <= 0;
			end
			else if(!i_wr && i_rd && !empty) begin // successful read
				full  <= 0;
				empty <= (rptr_nxt == wptr);
			end
			else if(i_wr && i_rd  && empty) begin // successful write, failed read
				full  <= 0;
				empty <= 0;
			end
			else if(i_wr && i_rd && !empty) begin
				full  <= full;
				empty <= 0;
		    end
		end
	end

//
//
// **** FORMAL VERIFICATION ****
//
`ifdef FORMAL

// include option to turn assumes into asserts
`ifdef FIFO_SYNC
`define ASSUME assume
`else 
`define ASSUME assert
`endif
		
	
	
	// set up f_past_valid to determine if $past will return
	// a valid result
	reg f_past_valid;
	initial f_past_valid = 0;
	always@(posedge i_clk)
		f_past_valid <= 1;

	// force initialize in reset state
	always@*
		if(!f_past_valid)
			`ASSUME(!i_rstn);

	// set up clock
	reg f_last_clk;
	always@($global_clock) begin
		f_last_clk <= i_clk;
		assume(i_clk == !f_last_clk);
	end

	// assume synchronous inputs
	always@($global_clock) begin
		if(!$rose(i_clk)) begin
			`ASSUME($stable(i_rstn));
			`ASSUME($stable(i_wr));
			`ASSUME($stable(i_data));
			`ASSUME($stable(i_rd));
		end
	end


	// check the fill level
	wire [ADDR_WIDTH-1:0] f_fill;
	assign f_fill = wptr - rptr;
	always@(posedge i_clk)
		if(f_past_valid)
			assert(f_fill == fill);

	// check the empty flag
	always@(posedge i_clk) begin
		if(f_past_valid) begin
			if(f_fill == 0) begin
				assert(empty);
			end
			else begin
				assert(!empty);
			end
		end
	end

	// check the full flag
	always@(posedge i_clk) begin
		if(f_fill == {ADDR_WIDTH{1'b1}}) begin
			assert(full);
		end 
		else begin
			assert(!full);
		end
	end

	// check error flag
	always@(posedge i_clk) begin
		if(f_past_valid) begin
			if($past(!i_rstn))
				assert(!o_error);
			else begin
				// check underrun behavior
				if(($past(i_rd)) && ($past(fill == 0))) begin
					assert(o_error);
					assert(rptr == $past(rptr));
				end

				// check overrun behavior
				// - not an error if fifo is full and simulataneous read/write
				if(($past(i_wr)) && $past(!i_rd) && ($past(fill == {ADDR_WIDTH{1'b1}}))) begin
					assert(o_error);
					assert(wptr == $past(wptr));
				end
			end
		end
	end

`endif

endmodule // fifo_sync