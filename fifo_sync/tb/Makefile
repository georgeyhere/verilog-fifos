SHELL := /bin/bash 

.PHONY: compile test sim formal clean

compile:
	vlog ../rtl/fifo_sync.v 

formal:
	sby formal/fifo_sync.sby -f

clean: 
	rm -rf formal/fifo_sync_cover_fifo  
	rm -rf formal/fifo_sync_prove_fifo 
