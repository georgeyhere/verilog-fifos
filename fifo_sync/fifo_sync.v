`default_nettype none
//
//
module fifo_sync
	#(parameter DATA_WIDTH         = 8,
      parameter ADDR_WIDTH         = 9,
      parameter ALMOSTFULL_OFFSET  = 2,
      parameter ALMOSTEMPTY_OFFSET = 2
	  )
	(
    input  wire                   i_clk,
    input  wire                   i_rstn,
                   
    input  wire                   i_wr,
    input  wire [DATA_WIDTH-1:0]  i_data,
                  
    input  wire                   i_rd,
    output reg  [DATA_WIDTH-1:0]  o_data,

    output wire                   o_full,
    output wire                   o_almostfull,
    output wire                   o_empty,
    output wire                   o_almostempty
	);

	localparam FIFO_DEPTH = (1<<ADDR_WIDTH);

	reg  [DATA_WIDTH-1:0] mem [0:FIFO_DEPTH-1];
 	wire [DATA_WIDTH-1:0] rdata;


	reg  [ADDR_WIDTH  :0] fill;     
	
	reg  [ADDR_WIDTH-1:0] wptr;             
	reg  [ADDR_WIDTH-1:0] rptr;

// distributed ram
	always@(posedge i_clk) begin
		mem[wptr] <= i_data;
	end
	assign rdata = mem[rptr];
	always@(posedge i_clk) begin // output register
		o_data <= rdata;
	end

// write pointer
	always@(posedge i_clk, negedge i_rstn) begin
		if(!i_rstn) begin
			wptr <= 0;
		end
		else begin
			wptr <= (i_wr) ? wptr+1 : wptr;
		end
	end

// read pointer
	always@(posedge i_clk, negedge i_rstn) begin
		if(!i_rstn) begin
			rptr <= 0;
		end
		else begin
			rptr <= (i_rd) ? rptr+1 : rptr;
		end
	end

// fill and status
	always@(posedge i_clk, negedge i_rstn) begin
		if(!i_rstn) begin
			fill <= 0;
		end
		else if (i_rd && !i_wr) begin
			fill <= fill - 1;
		end
		else if (!i_rd && i_wr) begin
			fill <= fill + 1;
		end
	end

	assign o_full        = (fill == FIFO_DEPTH);
	assign o_almostfull  = (fill == FIFO_DEPTH-ALMOSTFULL_OFFSET);
	assign o_empty       = (fill == 0);
	assign o_almostempty = (fill <= ALMOSTEMPTY_OFFSET);

endmodule // fifo_sync