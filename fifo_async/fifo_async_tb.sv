module fifo_async_tb();
    
    

    
//
// DUT I/O
// 
    parameter DATA_WIDTH = 2;
    parameter ADDR_WIDTH = 4;
    localparam MEM_DEPTH = $pow(2, ADDR_WIDTH);

    logic                  wclk, wrstn;
    logic                  wr;
    logic [DATA_WIDTH-1:0] wdata;
    logic                  wfull;

    logic                  rclk, rrstn;
    logic                  rd;
    logic [DATA_WIDTH-1:0] rdata;
    logic                  rempty;

//
// DUT instantiation
//
    fifo_async #(DATA_WIDTH, ADDR_WIDTH) 
    DUT (
    .i_wclk   (wclk),
    .i_wrstn  (wrstn),
    .i_wr     (wr),
    .i_wdata  (wdata),
    .o_wfull  (wfull),
    
    .i_rclk   (rclk),
    .i_rrstn  (rrstn),
    .i_rd     (rd),
    .o_rdata  (rdata),
    .o_rempty (rempty)
    );



//
// Testbench Setup
//
     localparam TESTRUNS = 5;  // # of runs
     localparam W_PERIOD = 10; // write clock period
     localparam R_PERIOD = 20; // read clock period
   
     logic [DATA_WIDTH-1:0] test_queue[$]; // queue for writing data
     logic [DATA_WIDTH-1:0] test_expected; // expected data from read side
   
     // create dumpfile
     initial begin
         $dumpfile("fifo_async.vcd");
         $dumpvars(0, fifo_async_tb);
     end
   
     // generate independent read/write clocks
     initial begin
       wclk = 0;
       rclk = 0;
   
       fork 
         forever #(W_PERIOD/2) wclk = ~wclk;
         forever #(R_PERIOD/2) rclk = ~rclk;
       join
     end


//
// Write test_queue into FIFO
//
     initial begin
         wr    = 0;
         wdata = 0;
         wrstn = 0;
 
         repeat(5) @(posedge wclk);
 
         wrstn = 1;
 
         for (int i=0; i<TESTRUNS; i++) begin
             for(int j=0; j<MEM_DEPTH; j++) begin
                 @(posedge wclk) begin
                     // write to DUT on every other clock
                     if(j%2 == 0) wr <= 1;
                     else         wr <= 0;

                     // store writes into queue     
                     if(wr) begin
                         wdata = $urandom; 
                         //if(!o_wfull) 
                         test_queue.push_front(wdata);
                     end
                 end
             end
             #1us;
         end
     end

//
// Read from FIFO; compare against test_expected
//
     initial begin
         rd    = 0;
         rrstn = 0;
   
         repeat(5) @(posedge rclk);
   
         rrstn = 1;
   
         for(int i=0; i<TESTRUNS; i++) begin
             for(int j=0; j<MEM_DEPTH; j++) begin
                  // read every other clock
                  if(i%2 == 0) rd <= 1;
                  else         rd <= 0;
                  
                  // check each read
                  if(rd) begin
                      test_expected = test_queue.pop_back();
                      $display("Expected rdata: %h, Actual rdata: %h", test_expected, rdata);
                      assert(rdata == test_expected)
                      else $error("Checking failed: expected wdata = %h, rdata = %h", test_expected, rdata);
                  end
             end
             #1us;
         end
         $finish;
     end

endmodule
