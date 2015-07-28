PROG ?= gcd
# PROG = PipelineFIFO
# PROG = BypassFIFO
# PROG = PipeFwdBwd


.PHONY: default

default: $(PROG)

all: gcd  PipelineFIFO  BypassFIFO  PipeFwdBwd

gcd:
	runghc  Main  100  Progs/GCD.kbsv   >  foo
	diff -s  log_GCD  foo

PipelineFIFO:
	runghc  Main  100  Progs/PipelineFIFO.kbsv   >  foo
	diff -s  log_PipelineFIFO  foo

BypassFIFO:
	runghc  Main  100  Progs/BypassFIFO.kbsv   >  foo
	diff -s  log_BypassFIFO  foo

PipeFwdBwd:
	runghc  Main  100  Progs/PipeFwdBwd.kbsv   >  foo
	diff -s  log_PipeFwdBwd  foo
