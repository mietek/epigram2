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


Epitome.pdf : Epitome.tex Epitome.bib
	pdflatex Epitome
	bibtex Epitome
	pdflatex Epitome
	pdflatex Epitome

Epitome.dvi : Epitome.tex
	latex Epitome
	bibtex Epitome
	latex Epitome
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
	rm -f *.o *.hers *.hi\
	      *.aux *.bbl\
	      *.blg *.log *.ptb\
	      Epitome.tex 

ifeq ($(MAKECMDGOALS),clean)
else ifeq ($(MAKECMDGOALS),dvi)
else
include .depend
endif
