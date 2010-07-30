################
#### PDFLaTeX

LATEX = latex
LATEXC = pdflatex
LATEX_OPTS = #-interaction=nonstopmode
LHS2TEX = lhs2TeX
LHS2TEX_OPTS = --poly
GHC = ghc
GHC_OPTS = -package mtl

revised : type-inference-revised.lhs lib-short.bib
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference-revised.tex type-inference-revised.lhs
	$(LATEXC) $(LATEX_OPTS) type-inference-revised
	bibtex type-inference-revised
	$(LATEXC) $(LATEX_OPTS) type-inference-revised
	if egrep Rerun type-inference-revised.log; then $(LATEXC) $(LATEX_OPTS) type-inference-revised; fi

quick : type-inference-revised.lhs
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference-revised.tex type-inference-revised.lhs
	$(LATEXC) $(LATEX_OPTS) type-inference-revised

test  : type-inference-revised.lhs
	$(GHC) $(GHC_OPTS) -o type-inference-revised type-inference-revised.lhs
	./type-inference-revised

final : type-inference-final.lhs
	$(LHS2TEX) $(LHS2TEX_OPTS) -o msfp31v-gundry.tex type-inference-final.lhs
	latex msfp31v-gundry
	latex msfp31v-gundry
	latex msfp31v-gundry
	dvips -Pdownload35 -t letter -o msfp31v-gundry.ps msfp31v-gundry.dvi
	ps2pdf msfp31v-gundry.ps msfp31v-gundry.pdf

original : type-inference.lhs lib.bib
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference.tex type-inference.lhs
	$(LATEXC) $(LATEX_OPTS) type-inference
	bibtex type-inference
	$(LATEXC) $(LATEX_OPTS) type-inference
	if egrep Rerun type-inference.log; then $(LATEXC) $(LATEX_OPTS) type-inference; fi

original-quick : type-inference.lhs
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference.tex type-inference.lhs
	$(LATEXC) $(LATEX_OPTS) type-inference

original-test  : type-inference.lhs
	$(GHC) $(GHC_OPTS) -o type-inference type-inference.lhs
	./type-inference

dvi   : type-inference.lhs lib.bib
	$(LHS2TEX) $(LHS2TEX_OPTS) -o type-inference.tex type-inference.lhs
	$(LATEX) $(LATEX_OPTS) type-inference
	bibtex type-inference
	$(LATEX) $(LATEX_OPTS) type-inference
	if egrep Rerun type-inference.log; then $(LATEX) $(LATEX_OPTS) type-inference; fi

