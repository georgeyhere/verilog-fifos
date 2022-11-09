onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {DUT Parameters} /fifo_async_tb/DATA_WIDTH
add wave -noupdate -expand -group {DUT Parameters} /fifo_async_tb/ADDR_WIDTH
add wave -noupdate -expand -group {DUT Parameters} /fifo_async_tb/MEM_DEPTH
add wave -noupdate -expand -group {Test Parameters} /fifo_async_tb/TESTRUNS
add wave -noupdate -expand -group {Test Parameters} /fifo_async_tb/W_PERIOD
add wave -noupdate -expand -group {Test Parameters} /fifo_async_tb/R_PERIOD
add wave -noupdate -divider WRITE
add wave -noupdate /fifo_async_tb/wclk
add wave -noupdate -expand -group {Write Interface} /fifo_async_tb/wrstn
add wave -noupdate -expand -group {Write Interface} -radix unsigned /fifo_async_tb/wfill
add wave -noupdate -expand -group {Write Interface} /fifo_async_tb/wfull
add wave -noupdate -expand -group {Write Interface} /fifo_async_tb/walmostfull
add wave -noupdate -expand -group {Write Interface} /fifo_async_tb/wr
add wave -noupdate -expand -group {Write Interface} -radix hexadecimal /fifo_async_tb/wdata
add wave -noupdate -group {Write CDC} /fifo_async_tb/DUT/wq1_rptr
add wave -noupdate -group {Write CDC} /fifo_async_tb/DUT/wq2_rptr
add wave -noupdate -group {Write Pointers} /fifo_async_tb/DUT/wbin
add wave -noupdate -group {Write Pointers} /fifo_async_tb/DUT/wptr
add wave -noupdate -divider READ
add wave -noupdate /fifo_async_tb/rclk
add wave -noupdate -expand -group {Read Interface} /fifo_async_tb/rrstn
add wave -noupdate -expand -group {Read Interface} -radix unsigned /fifo_async_tb/rfill
add wave -noupdate -expand -group {Read Interface} /fifo_async_tb/rempty
add wave -noupdate -expand -group {Read Interface} /fifo_async_tb/ralmostempty
add wave -noupdate -expand -group {Read Interface} /fifo_async_tb/rd
add wave -noupdate -expand -group {Read Interface} -radix hexadecimal /fifo_async_tb/rdata
add wave -noupdate -group {Read CDC} /fifo_async_tb/DUT/rq1_wptr
add wave -noupdate -group {Read CDC} /fifo_async_tb/DUT/rq2_wptr
add wave -noupdate -group {Read Pointers} -radix decimal /fifo_async_tb/DUT/rbin
add wave -noupdate -group {Read Pointers} /fifo_async_tb/DUT/rptr
add wave -noupdate -divider INTERNAL
add wave -noupdate /fifo_async_tb/DUT/mem
add wave -noupdate -radix unsigned /fifo_async_tb/DUT/waddr
add wave -noupdate -radix unsigned /fifo_async_tb/DUT/raddr
add wave -noupdate -divider TESTBENCH
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {130 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {784 ps} {1128 ps}
