################
#### PDFLaTeX

PDFTEX = pdflatex
PSTEX = latex
LATEXOPTS = #-interaction=nonstopmode


################
## Sources

SRCS=paper.tex
DEPS := $(wildcard *.tex)

################
## Make machinery

.SUFFIXES : .tex .pdf .ps

DOCPS := $(SRCS:.tex=.pdf)
DOCPDF := $(SRCS:.tex=.ps)

.tex.pdf:
	$(PDFTEX) $<
	bibtex $*
	$(PDFTEX) $<
	if egrep Rerun $*.log; then $(PDFTEX) $< ; fi

.tex.ps:
	$(PSTEX) $<
	bibtex $*
	$(PSTEX) $<
	if egrep Rerun $*.log; then $(PSTEX) $< ; fi
	dvips -t letter $*.dvi

################
## Targets

all: paper

paper.pdf: $(DEPS) pig.sty paper.bib

paper.ps: $(DEPS) pig.sty paper.bib

paper: $(DOCPDF) $(DOCPS)


