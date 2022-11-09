module fifo_async_tb();

    parameter DATA_WIDTH = 8;
    parameter ADDR_WIDTH = 4;
    parameter ALMOSTFULL_OFFSET  = 2;
    parameter ALMOSTEMPTY_OFFSET = 2;
    
    localparam TESTRUNS = 50;  // # of words to write
    localparam W_PERIOD = 5;  // write clock period
    localparam R_PERIOD = 20; // read clock period


// DUT I/O
    logic                  wclk, wrstn;
    logic                  wr;
    logic [DATA_WIDTH-1:0] wdata;
    logic [ADDR_WIDTH  :0] wfill;
    logic                  wfull;
    logic                  walmostfull;

    logic                  rclk, rrstn;
    logic                  rd;
    logic [DATA_WIDTH-1:0] rdata;
    logic [ADDR_WIDTH  :0] rfill;
    logic                  rempty;
    logic                  ralmostempty;

//
// DUT instantiation
//
    fifo_async #(
        .DATA_WIDTH         (DATA_WIDTH),
        .PTR_WIDTH          (ADDR_WIDTH),
        .ALMOSTFULL_OFFSET  (ALMOSTFULL_OFFSET),
        .ALMOSTEMPTY_OFFSET (ALMOSTEMPTY_OFFSET) 
    ) 
    DUT (
        .i_wclk         (wclk),
        .i_wrstn        (wrstn),
        .i_wr           (wr),
        .i_wdata        (wdata),
        .o_wfill        (wfill),
        .o_wfull        (wfull),
        .o_walmostfull  (walmostfull),
        
        .i_rclk         (rclk),
        .i_rrstn        (rrstn),
        .i_rd           (rd),
        .o_rdata        (rdata),
        .o_rfill        (rfill),
        .o_rempty       (rempty),
        .o_ralmostempty (ralmostempty)
    );
   
    initial begin
        $dumpfile("fifo_async.vcd");
        $dumpvars(0, fifo_async_tb);
    end
   
// CLOCK GENERATION
    initial begin
      wclk = 0;
      rclk = 0;
   
      fork 
        forever #(W_PERIOD/2) wclk = ~wclk;
        forever #(R_PERIOD/2) rclk = ~rclk;
      join
    end

// FLAG MONITORING
    initial begin 
        $monitor("t=%4d | wfill=%d  wfull=%b  walmostfull=%b\n         rfill=%d  rempty=%b  ralmostempty=%b\n",
                 $realtime, wfill, wfull, walmostfull, rfill, rempty, ralmostempty);
        //$monitor("t=%4d | wfill = %d  wfull  = %b  walmostfull  = %b", $realtime, wfill, wfull, walmostfull);
        //$monitor("      | rfill = %d  rempty = %b  ralmostempty = %b\n", rfill, rempty, ralmostempty);
    end 



    localparam MEM_DEPTH = $pow(2, (ADDR_WIDTH-1));

    typedef struct {
        logic [DATA_WIDTH-1:0] queue [$];
        logic [DATA_WIDTH-1:0] data;
        logic [DATA_WIDTH-1:0] expected;
        bit ready;
        int count;
    } fifo;
    fifo wrInst, rdInst;

// Write to FIFO
    initial begin
        wr    = 0;
        wdata = 0;
        wrstn = 0;
        wrInst.ready = 0;
        wrInst.count = 0;
        #(W_PERIOD);
        wrInst.ready = 1;
        @(posedge wclk) wrstn <= 1;
    end 

    always@(posedge wclk) begin 
        if(wrInst.ready & rdInst.ready) begin 
            if(wrInst.count < TESTRUNS) begin 
                wr <= (!walmostfull);
                if(!walmostfull) begin 
                    wdata = $urandom;
                    wrInst.queue.push_front(wdata);
                    wrInst.count++;
                end 
            end 
            else wr <= 0;
        end 
    end 


// Read from FIFO 
    initial begin 
        rd    = 0;
        rdata = 0;
        rrstn = 0;
        rdInst.ready = 0;
        rdInst.data  = 0;
        rdInst.count = 0;
        #(R_PERIOD);
        rdInst.ready = 1;
        @(posedge rclk) rrstn <= 1;
    end 

    always@(posedge rclk) begin 
        if(wrInst.ready & rdInst.ready) begin 
            if(rdInst.count < TESTRUNS) begin 
                rd <= (!ralmostempty);

                if(!rempty) begin   
                    #1;
                    rdInst.data = rdata;
                    rdInst.expected = wrInst.queue.pop_back();
                    $display("%d: Expected rdata: %h, Actual rdata: %h", rdInst.count, rdInst.expected, rdInst.data);
                    assert(rdInst.expected == rdInst.data)
                    else begin 
                        $error("Checking failed: expected wdata = %h, rdata = %h", rdInst.expected, rdInst.data);
                        #(R_PERIOD/2);
                        $stop();
                    end
                    rdInst.count++;
                end 

                else begin 
                    rd <= 0;
                end 
            end 
            else begin 
                $display("\nTest Complete!\n");
                $finish();
            end 
        end 
    end 

endmodule
