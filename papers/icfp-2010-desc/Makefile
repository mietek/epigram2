################
#### PDFLaTeX

LATEXC = pdflatex
LATEXOPTS = -interaction=nonstopmode


paper : paper.tex paper.bib
	$(LATEXC) $(LATEXOPTS) paper
	bibtex paper
	$(LATEXC) $(LATEXOPTS) paper
	if egrep Rerun paper.log; then $(LATEXC) $(LATEXOPTS) paper; fi
