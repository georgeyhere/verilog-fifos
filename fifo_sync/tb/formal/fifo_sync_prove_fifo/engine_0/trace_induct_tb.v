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
  reg [0:0] PI_i_rd;
  reg [0:0] PI_i_clk;
  reg [31:0] PI_i_data;
  reg [0:0] PI_i_rstn;
  reg [0:0] PI_i_wr;
  fifo_sync UUT (
    .i_rd(PI_i_rd),
    .i_clk(PI_i_clk),
    .i_data(PI_i_data),
    .i_rstn(PI_i_rstn),
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
    // UUT.$auto$clk2fflogic.\cc:148:execute$mem#0#past_clk#/i_clk$777  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:164:execute$mem#0#en_q$781  = 32'b00000000000000000000000000000000;
    // UUT.$auto$clk2fflogic.\cc:167:execute$mem#0#addr_q$783  = 10'b1000000000;
    // UUT.$auto$clk2fflogic.\cc:170:execute$mem#0#data_q$785  = 32'b00000000000000000000000000000000;
    // UUT.$auto$clk2fflogic.\cc:62:sample_control$$auto$rtlil .\cc:2371:Not$800#sampled$801  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/o_empty[0:0]#sampled$827  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/o_fill[10:0]#sampled$863  = 11'b00000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/o_full[0:0]#sampled$845  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/rptr[9:0]#sampled$809  = 10'b0000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/wptr[9:0]#sampled$791  = 10'b0000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/f_past_valid#sampled$919  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/o_empty#sampled$825  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/o_fill#sampled$861  = 11'b00000010000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/o_full#sampled$843  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/rptr#sampled$807  = 10'b1111101110;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/wptr#sampled$789  = 10'b0101111100;
    // UUT.$formal$fifo_sync.\v:148$29_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:154$30_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:168$36_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:192$48_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:195$49_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:271$51_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:274$52_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:279$53_EN  = 1'b0;
    UUT._witness_.anyinit_procdff_685 = 1'b0;
    UUT._witness_.anyinit_procdff_686 = 1'b0;
    UUT._witness_.anyinit_procdff_687 = 1'b0;
    UUT._witness_.anyinit_procdff_688 = 1'b0;
    UUT._witness_.anyinit_procdff_689 = 1'b0;
    UUT._witness_.anyinit_procdff_690 = 1'b0;
    UUT._witness_.anyinit_procdff_691 = 1'b0;
    UUT._witness_.anyinit_procdff_692 = 1'b0;
    UUT._witness_.anyinit_procdff_693 = 1'b0;
    UUT._witness_.anyinit_procdff_695 = 1'b0;
    UUT._witness_.anyinit_procdff_697 = 1'b0;
    UUT._witness_.anyinit_procdff_699 = 1'b1;
    UUT._witness_.anyinit_procdff_701 = 1'b0;
    UUT._witness_.anyinit_procdff_703 = 1'b0;
    UUT._witness_.anyinit_procdff_705 = 1'b0;
    UUT._witness_.anyinit_procdff_707 = 1'b0;
    UUT._witness_.anyinit_procdff_709 = 1'b0;
    UUT._witness_.anyinit_procdff_711 = 1'b0;
    UUT._witness_.anyinit_procdff_713 = 1'b0;
    UUT._witness_.anyinit_procdff_715 = 1'b0;
    UUT._witness_.anyinit_procdff_717 = 1'b0;
    UUT._witness_.anyinit_procdff_719 = 1'b0;
    UUT._witness_.anyinit_procdff_721 = 1'b0;
    UUT._witness_.anyinit_procdff_723 = 1'b0;
    UUT._witness_.anyinit_procdff_724 = 1'b0;
    UUT._witness_.anyinit_procdff_725 = 32'b00000000000000000000000000000000;
    UUT._witness_.anyinit_procdff_726 = 1'b1;
    UUT._witness_.anyinit_procdff_727 = 1'b1;
    UUT._witness_.anyinit_procdff_728 = 11'b00000010000;
    UUT._witness_.anyinit_procdff_729 = 32'b10000000000000000000000000000000;
    UUT._witness_.anyinit_procdff_730 = 1'b0;
    UUT._witness_.anyinit_procdff_732 = 1'b0;
    UUT._witness_.anyinit_procdff_734 = 1'b0;
    UUT._witness_.anyinit_procdff_736 = 1'b0;
    UUT._witness_.anyinit_procdff_738 = 1'b0;
    UUT._witness_.anyinit_procdff_740 = 1'b0;
    UUT._witness_.anyinit_procdff_742 = 1'b0;
    UUT._witness_.anyinit_procdff_743 = 1'b0;
    UUT._witness_.anyinit_procdff_744 = 1'b0;
    UUT._witness_.anyinit_procdff_745 = 1'b1;
    UUT._witness_.anyinit_procdff_746 = 1'b1;
    UUT._witness_.anyinit_procdff_748 = 1'b0;
    UUT.f_clk_count = 5'b00000;
    UUT.f_past_valid_gbl = 1'b1;
    UUT.f_const_addr = 11'b11101111101;
    UUT.f_const_next = 32'b00111111111110111111111111111111;
    UUT.f_const_first = 32'b10111111111111111111111111111111;
    UUT.mem[10'b1111101110] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1101111110] = 32'b00111111111110111111111111111111;
    UUT.mem[10'b1101111101] = 32'b10111111111111111111111111111111;
    UUT.mem[10'b1111101111] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111110000] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111110001] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111110010] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111110011] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111110100] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111110101] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111110110] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111110111] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111111000] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111111001] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111111010] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111111011] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111111100] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111111101] = 32'b10000000000000000000000000000000;
    UUT.mem[10'b1111111110] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b1111111111] = 32'b00111111111110111111111111111111;
    UUT.mem[10'b0000000000] = 32'b10011111111111111111111111111111;

    // state 0
    PI_i_rd = 1'b1;
    PI_i_clk = 1'b0;
    PI_i_data = 32'b00000000000000000000000000000000;
    PI_i_rstn = 1'b1;
    PI_i_wr = 1'b0;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 2
    if (cycle == 1) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 3
    if (cycle == 2) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 4
    if (cycle == 3) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 5
    if (cycle == 4) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 6
    if (cycle == 5) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 7
    if (cycle == 6) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 8
    if (cycle == 7) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 9
    if (cycle == 8) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 10
    if (cycle == 9) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 11
    if (cycle == 10) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 12
    if (cycle == 11) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 13
    if (cycle == 12) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 14
    if (cycle == 13) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 15
    if (cycle == 14) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 16
    if (cycle == 15) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 17
    if (cycle == 16) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 18
    if (cycle == 17) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 19
    if (cycle == 18) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 20
    if (cycle == 19) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 21
    if (cycle == 20) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 22
    if (cycle == 21) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 23
    if (cycle == 22) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 24
    if (cycle == 23) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 25
    if (cycle == 24) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 26
    if (cycle == 25) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 27
    if (cycle == 26) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 28
    if (cycle == 27) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 29
    if (cycle == 28) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 30
    if (cycle == 29) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 31
    if (cycle == 30) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 32
    if (cycle == 31) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 33
    if (cycle == 32) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 34
    if (cycle == 33) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 35
    if (cycle == 34) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 36
    if (cycle == 35) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 37
    if (cycle == 36) begin
      PI_i_rd <= 1'b0;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b10111111111111111111111111111111;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 38
    if (cycle == 37) begin
      PI_i_rd <= 1'b0;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b10111111111111111111111111111111;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 39
    if (cycle == 38) begin
      PI_i_rd <= 1'b0;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 40
    if (cycle == 39) begin
      PI_i_rd <= 1'b0;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 41
    if (cycle == 40) begin
      PI_i_rd <= 1'b0;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 42
    if (cycle == 41) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b10111111111111111111111111111111;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 43
    if (cycle == 42) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b10111111111111111111111111111111;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b0;
    end

    // state 44
    if (cycle == 43) begin
      PI_i_rd <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b1;
      PI_i_wr <= 1'b1;
    end

    // state 45
    if (cycle == 44) begin
      PI_i_rd <= 1'b0;
      PI_i_clk <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
      PI_i_rstn <= 1'b0;
      PI_i_wr <= 1'b0;
    end

    genclock <= cycle < 45;
    cycle <= cycle + 1;
  end
endmodule
