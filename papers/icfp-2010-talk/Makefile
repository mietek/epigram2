################
#### PDFLaTeX

PDFTEX = pdflatex

################
## Sources

SRCS=levitation.tex
DEPS := $(wildcard *.tex) pig.sty

################
## Make machinery

.SUFFIXES : .tex .pdf

DOCPDF := $(SRCS:.tex=.pdf)

.tex.pdf:
	$(PDFTEX) $<
	$(PDFTEX) $<
	if egrep Rerun $*.log; then $(PDFTEX) $< ; fi

################
## Targets

all: levitation

levitation.pdf: $(DEPS)

levitation: $(DOCPDF)


