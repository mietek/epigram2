################
#### PDFLaTeX

PDFTEX = pdflatex
PSTEX = latex
LATEXOPTS = #-interaction=nonstopmode


################
## Sources

SRCS=ydtm-rev.tex
DEPS := $(wildcard *.tex)
BIBS := $(wildcard *.bib)

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

paper.pdf: $(DEPS) pig.sty $(BIBS)

paper.ps: $(DEPS) pig.sty  $(BIBS)

paper: $(DOCPDF) $(DOCPS)


