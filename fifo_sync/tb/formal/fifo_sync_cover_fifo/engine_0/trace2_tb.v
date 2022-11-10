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
  reg [0:0] PI_i_wr;
  reg [0:0] PI_i_rstn;
  reg [0:0] PI_i_clk;
  reg [0:0] PI_i_rd;
  reg [31:0] PI_i_data;
  fifo_sync UUT (
    .i_wr(PI_i_wr),
    .i_rstn(PI_i_rstn),
    .i_clk(PI_i_clk),
    .i_rd(PI_i_rd),
    .i_data(PI_i_data)
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
    // UUT.$auto$clk2fflogic.\cc:148:execute$mem#0#past_clk#/i_clk$777  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:164:execute$mem#0#en_q$781  = 32'b00000000000000000000000000000000;
    // UUT.$auto$clk2fflogic.\cc:167:execute$mem#0#addr_q$783  = 10'b0000000000;
    // UUT.$auto$clk2fflogic.\cc:170:execute$mem#0#data_q$785  = 32'b00000000000000000000000000000000;
    // UUT.$auto$clk2fflogic.\cc:62:sample_control$$auto$rtlil .\cc:2371:Not$800#sampled$801  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0$formal$fifo_sync .\v:289$57_CHECK[0:0]$334#sampled$891  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0$formal$fifo_sync .\v:290$58_CHECK[0:0]$336#sampled$881  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0$formal$fifo_sync .\v:295$59_CHECK[0:0]$343#sampled$941  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0$formal$fifo_sync .\v:295$59_EN[0:0]$344#sampled$971  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0$formal$fifo_sync .\v:299$60_CHECK[0:0]$349#sampled$981  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/o_empty[0:0]#sampled$827  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/o_fill[10:0]#sampled$863  = 11'b00000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/o_full[0:0]#sampled$845  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/rptr[9:0]#sampled$809  = 10'b0000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$0/wptr[9:0]#sampled$791  = 10'b0000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$$formal$fifo_sync .\v:299$60_EN#sampled$969  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/f_past_valid#sampled$919  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/i_rd#sampled$901  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/i_rstn#sampled$931  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/i_wr#sampled$911  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/o_empty#sampled$825  = 1'b1;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/o_fill#sampled$861  = 11'b00000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/o_full#sampled$843  = 1'b0;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/rptr#sampled$807  = 10'b0000000000;
    // UUT.$auto$clk2fflogic.\cc:86:sample_data$/wptr#sampled$789  = 10'b0000000000;
    // UUT.$formal$fifo_sync.\v:148$29_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:154$30_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:168$36_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:192$48_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:195$49_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:271$51_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:274$52_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:279$53_EN  = 1'b0;
    // UUT.$formal$fifo_sync.\v:303$61_EN  = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_880 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_890 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_900 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_910 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_930 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_940 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_950 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_960 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_980 = 1'b0;
    UUT._witness_.anyinit_auto_clk2fflogic_cc_91_sample_data_990 = 1'b0;
    UUT._witness_.anyinit_procdff_665 = 1'b0;
    UUT._witness_.anyinit_procdff_666 = 1'b0;
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
    UUT._witness_.anyinit_procdff_699 = 1'b0;
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
    UUT._witness_.anyinit_procdff_724 = 1'b1;
    UUT._witness_.anyinit_procdff_725 = 32'b10000000000000000000000000000000;
    UUT._witness_.anyinit_procdff_726 = 1'b1;
    UUT._witness_.anyinit_procdff_727 = 1'b0;
    UUT._witness_.anyinit_procdff_728 = 11'b00000000000;
    UUT._witness_.anyinit_procdff_729 = 32'b00000000000000000000000000000000;
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
    UUT._witness_.anyinit_procdff_746 = 1'b0;
    UUT._witness_.anyinit_procdff_748 = 1'b0;
    UUT.f_clk_count = 5'b00000;
    UUT.f_past_valid_gbl = 1'b0;
    UUT.f_const_addr = 11'b00000000000;
    UUT.f_const_next = 32'b00000000000000000000000000000000;
    UUT.f_const_first = 32'b00000000000000000000000000000000;
    UUT.mem[10'b0000000000] = 32'b00000000000000000000000000000000;
    UUT.mem[10'b0000000001] = 32'b00000000000000000000000000000000;

    // state 0
    PI_i_wr = 1'b0;
    PI_i_rstn = 1'b1;
    PI_i_clk = 1'b0;
    PI_i_rd = 1'b0;
    PI_i_data = 32'b00000000000000000000000000000000;
  end
  always @(posedge clock) begin
    // state 1
    if (cycle == 0) begin
      PI_i_wr <= 1'b1;
      PI_i_rstn <= 1'b1;
      PI_i_clk <= 1'b1;
      PI_i_rd <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
    end

    // state 2
    if (cycle == 1) begin
      PI_i_wr <= 1'b1;
      PI_i_rstn <= 1'b1;
      PI_i_clk <= 1'b0;
      PI_i_rd <= 1'b1;
      PI_i_data <= 32'b00000000000000000000000000000000;
    end

    // state 3
    if (cycle == 2) begin
      PI_i_wr <= 1'b0;
      PI_i_rstn <= 1'b0;
      PI_i_clk <= 1'b1;
      PI_i_rd <= 1'b0;
      PI_i_data <= 32'b00000000000000000000000000000000;
    end

    genclock <= cycle < 3;
    cycle <= cycle + 1;
  end
endmodule
