HC      = ghc
HC_OPTS = -package mtl

SRCS := $(wildcard *.lhs) 
OBJS := $(SRCS:.lhs=.o) 

.SUFFIXES : .o .hs .hi .lhs .hc .s

Pig : $(OBJS)
	rm -f $@
	$(HC) -o $@ $(HC_OPTS) $(OBJS)

.depend : $(SRCS)
	$(HC) -M -dep-makefile .depend $(SRCS)

dvi : Epitome.dvi


Epitome.pdf : Epitome.tex
	pdflatex Epitome

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

clean:
	rm -f *.o *.hers *.hi

ifeq ($(MAKECMDGOALS),clean)
else ifeq ($(MAKECMDGOALS),dvi)
else
include .depend
endif
