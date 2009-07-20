HC      = ghc
HC_OPTS = -package mtl

SRCS := $(wildcard *.lhs) 
OBJS := $(SRCS:.lhs=.o) 

.SUFFIXES : .o .hs .hi .lhs .hc .s

Pig : $(OBJS)
	rm -f $@
	$(HC) -o $@ $(HC_OPTS) $(OBJS)

.depend : $(SRCS)
	ghc -M -dep-makefile .depend $(SRCS)

dvi : Epitome.dvi

Epitome.dvi : Epitome.tex
	latex Epitome

Epitome.tex : $(SRCS) stuff.fmt
	lhs2TeX --poly Epitome.lhs > Epitome.tex

# Standard suffix rules
.o.hi:
	@:

.lhs.o:
	$(HC) -c $< $(HC_OPTS)

.hs.o:
	$(HC) -c $< $(HC_OPTS)

.o-boot.hi-boot:
	@:

.lhs-boot.o-boot:
	$(HC) -c $< $(HC_OPTS)

.hs-boot.o-boot:
	$(HC) -c $< $(HC_OPTS)

include .depend

