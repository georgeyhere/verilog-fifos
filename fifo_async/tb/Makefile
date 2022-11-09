SHELL := /bin/bash

.PHONY: compile test formal clean

compile:
	vlog ../rtl/fifo_async.v
	vlog -sv fifo_async_tb.sv 

test: compile 
	vsim -c fifo_async_tb -do "run -all"

sim: compile
	vsim fifo_async_tb -do "do wave.do; run -all"

formal:
	sby formal/fifo_async.sby -f

clean:
	rm -rf formal/fifo_async_cover_fifo
	rm -rf formal/fifo_async_prove_fifo
	rm -rf fifo_async.vcd
	rm -rf transcript
	rm -rf vsim.wlf
	rm -rf work 
