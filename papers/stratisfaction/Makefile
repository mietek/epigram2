################
#### PDFLaTeX

TEX = pdflatex

################
## Sources

SRCS=paper.tex
DEPS := $(wildcard figure_*.tex)


################
## Make machinery

.SUFFIXES : .tex .pdf

DOC := $(SRCS:.tex=.pdf) 

.tex.pdf:
	$(TEX) $<
	if egrep "\bibliography" $<; then bibtex $*; fi
	$(TEX) $<
	if egrep Rerun $*.log; then $(TEX) $< ; fi

################
## Targets

all: paper

paper.pdf: $(DEPS) pig.sty Macros.tex stratisfaction.bib

paper: $(DOC)

