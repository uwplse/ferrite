DFYS := $(wildcard *.dfy)

all: $(DFYS:.dfy=.dll)

%.dll: %.dfy
	dafny /compile:0 $*.dfy
