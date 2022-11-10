onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /fifo_sync/i_clk
add wave -noupdate /fifo_sync/i_rstn
add wave -noupdate -divider {DUT Interface}
add wave -noupdate -radix hexadecimal /fifo_sync/i_wr
add wave -noupdate -radix hexadecimal /fifo_sync/i_data
add wave -noupdate -radix unsigned /fifo_sync/o_fill
add wave -noupdate /fifo_sync/i_rd
add wave -noupdate -radix hexadecimal /fifo_sync/o_data
add wave -noupdate -divider Formal
add wave -noupdate -expand -group {Formal Valid} /fifo_sync/f_past_valid
add wave -noupdate -expand -group {Formal Valid} /fifo_sync/f_addr_valid
add wave -noupdate -expand -group {FIFO status} -color Magenta /fifo_sync/f_first_in_fifo
add wave -noupdate -expand -group {FIFO status} -color Magenta /fifo_sync/f_second_in_fifo
add wave -noupdate -expand -group {FIFO status} -color Magenta /fifo_sync/f_both_in_fifo
add wave -noupdate /fifo_sync/f_wait_for_first_read
add wave -noupdate /fifo_sync/f_read_first
add wave -noupdate /fifo_sync/f_wait_for_second_read
add wave -noupdate /fifo_sync/f_read_second
add wave -noupdate /fifo_sync/f_const_addr
add wave -noupdate -radix hexadecimal /fifo_sync/f_const_first
add wave -noupdate /fifo_sync/f_const_next_addr
add wave -noupdate -radix hexadecimal /fifo_sync/f_const_next
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {70 ns} 0}
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
WaveRestoreZoom {0 ns} {126 ns}
