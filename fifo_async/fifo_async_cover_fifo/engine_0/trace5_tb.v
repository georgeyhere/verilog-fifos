`ifndef VERILATOR
module testbench;
  reg [4095:0] vcdfile;
  reg clock;
`else
module testbench(input clock, output reg genclock);
  initial genclock = 1;
`endif
  reg genclock = 1;
  reg [31:0] cycle = 0;
  reg [0:0] PI_i_wclk;
  reg [0:0] PI_i_rd;
  reg [0:0] PI_i_rrstn;
  reg [0:0] PI_i_wrstn;
  reg [1:0] PI_i_wdata;
  reg [0:0] PI_i_rclk;
  reg [0:0] PI_i_wr;
  fifo_async UUT (
    .i_wclk(PI_i_wclk),
    .i_rd(PI_i_rd),
    .i_rrstn(PI_i_rrstn),
    .i_wrstn(PI_i_wrstn),
    .i_wdata(PI_i_wdata),
    .i_rclk(PI_i_rclk),
    .i_wr(PI_i_wr)
  );
`ifndef VERILATOR
  initial begin
    if ($value$plusargs("vcd=%s", vcdfile)) begin
      $dumpfile(vcdfile);
      $dumpvars(0, testbench);
    end
    #5 clock = 0;
    while (genclock) begin
      #5 clock = 0;
      #5 clock = 1;
    end
  end
`endif
  initial begin
`ifndef VERILATOR
    #1;
`endif
    // UUT.$and$fifo_async.\v:0$163_Y  = 1'b1;
    // UUT.$and$fifo_async.\v:0$167_Y  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:124:execute$1101  = 2'b00;
    // UUT.$auto$clk2fflogic.\cc:127:execute$1103  = 4'b0000;
    // UUT.$auto$clk2fflogic.\cc:130:execute$1105  = 2'b00;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1109  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1119  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1129  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1197  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1214  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1282  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1299  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1309  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1319  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1329  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1339  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1349  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1359  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1369  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:156:execute$1403  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:168:execute$1111  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:168:execute$1216  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1125  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1135  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1152  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1169  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1186  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1203  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1220  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1237  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1254  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1271  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1288  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1305  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1315  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1325  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1335  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1345  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1375  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1392  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1409  = 5'b00000;
    // UUT.$auto$clk2fflogic.\cc:192:execute$1426  = 5'b00000;
    // UUT.$formal$fifo_async.\v:244$33_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:249$34_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:249$34_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:253$35_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:253$35_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:257$36_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:257$36_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:266$37_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:267$38_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:268$39_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:268$39_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:273$40_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:274$41_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:277$42_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:277$42_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:287$43_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:288$44_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:288$44_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:290$45_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:291$46_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:292$47_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:294$48_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:295$49_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:297$50_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:298$51_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:299$52_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:305$53_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:306$54_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:306$54_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:308$55_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:309$56_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:310$57_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:312$58_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:313$59_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:314$60_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:335$63_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:340$64_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:340$64_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:345$65_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:350$66_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:350$66_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:355$67_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:355$67_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:517$80_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:517$80_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:528$81_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:528$81_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:538$82_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:538$82_EN  = 1'b0;
    // UUT.$formal$fifo_async.\v:556$85_CHECK  = 1'b0;
    // UUT.$formal$fifo_async.\v:556$85_EN  = 1'b0;
    // UUT.$past$fifo_async.\v:268$9$0  = 2'b10;
    // UUT.$past$fifo_async.\v:274$12$0  = 1'b1;
    // UUT.$past$fifo_async.\v:277$13$0  = 2'b00;
    // UUT.$past$fifo_async.\v:278$14$0  = 1'b0;
    // UUT.$past$fifo_async.\v:517$15$0  = 1'b0;
    // UUT.$past$fifo_async.\v:517$16$0  = 1'b0;
    // UUT.$past$fifo_async.\v:538$21$0  = 1'b0;
    UUT.f_past_valid_gbl = 1'b0;
    UUT.f_rclk_count = 5'b11000;
    UUT.f_wclk_count = 5'b00000;
    UUT.f_const_first = 2'b00;
    UUT.f_const_addr = 4'b0000;
    UUT.f_const_next = 2'b00;
    UUT.mem[4'b0000] = 2'b00;
    UUT.mem[4'b0001] = 2'b00;

    // state 0
    PI_i_wclk = 1'b0;
    PI_i_rd = 1'b0;
    PI_i_rrstn = 1'b0;
    PI_i_wrstn = 1'b0;
    PI_i_wdata = 2'b00;
    PI_i_rclk = 1'b1;
    PI_i_wr = 1'b0;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 2
    if (cycle == 1) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 3
    if (cycle == 2) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 4
    if (cycle == 3) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 5
    if (cycle == 4) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 6
    if (cycle == 5) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 7
    if (cycle == 6) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 8
    if (cycle == 7) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 9
    if (cycle == 8) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 10
    if (cycle == 9) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 11
    if (cycle == 10) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 12
    if (cycle == 11) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 13
    if (cycle == 12) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 14
    if (cycle == 13) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 15
    if (cycle == 14) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 16
    if (cycle == 15) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 17
    if (cycle == 16) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 18
    if (cycle == 17) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 19
    if (cycle == 18) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 20
    if (cycle == 19) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 21
    if (cycle == 20) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 22
    if (cycle == 21) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 23
    if (cycle == 22) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 24
    if (cycle == 23) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 25
    if (cycle == 24) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 26
    if (cycle == 25) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 27
    if (cycle == 26) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 28
    if (cycle == 27) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 29
    if (cycle == 28) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 30
    if (cycle == 29) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 31
    if (cycle == 30) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b1;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b1;
    end

    // state 32
    if (cycle == 31) begin
      PI_i_wclk <= 1'b0;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b1;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 33
    if (cycle == 32) begin
      PI_i_wclk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_rrstn <= 1'b0;
      PI_i_wrstn <= 1'b1;
      PI_i_wdata <= 2'b00;
      PI_i_rclk <= 1'b0;
      PI_i_wr <= 1'b0;
    end

    genclock <= cycle < 33;
    cycle <= cycle + 1;
  end
endmodule
