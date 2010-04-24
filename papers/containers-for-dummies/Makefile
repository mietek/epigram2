MAIN = containers

################
#### PDFLaTeX

LATEXC = pdflatex
LATEXOPTS = #-interaction=nonstopmode


containers : $(MAIN).tex $(MAIN).bib
	$(LATEXC) $(LATEXOPTS) $(MAIN)
	bibtex $(MAIN)
	$(LATEXC) $(LATEXOPTS) $(MAIN)
	if egrep Rerun $(MAIN).log; then $(LATEXC) $(LATEXOPTS) $(MAIN); fi
