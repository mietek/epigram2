################
#### PDFLaTeX

LATEXC = pdflatex
LATEX_OPTS = #-interaction=nonstopmode
LHS2TEX = lhs2TeX
LHS2TEX_OPTS = --poly
GHC = ghc
GHC_OPTS = -package mtl

paper : type-inference.lhs lib.bib
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference.tex type-inference.lhs
	$(LATEXC) $(LATEX_OPTS) type-inference
	bibtex type-inference
	$(LATEXC) $(LATEX_OPTS) type-inference
	if egrep Rerun type-inference.log; then $(LATEXC) $(LATEX_OPTS) type-inference; fi

quick : type-inference.lhs
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference.tex type-inference.lhs
	$(LATEXC) $(LATEX_OPTS) type-inference

test  : type-inference.lhs
	$(GHC) $(GHC_OPTS) -o type-inference type-inference.lhs
	./type-inference