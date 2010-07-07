# 
# dossier make pour mckinna.{ps,pdf}
# 

ARTICLE=type-inference-revised

MAIN=$(ARTICLE)

LATEX=latex
LATEX_OPTS = #-interaction=nonstopmode

DVI = $(LATEX) $(LATEX_OPTS) $(MAIN) 
DVIPS=dvips -o - -f 
PS2PDF=ps2pdf -

LATEXC = pdflatex
PDF = $(LATEXC) $(LATEX_OPTS) $(MAIN) 

LHS2TEX = lhs2TeX
LHS2TEX_OPTS = --poly

GHC = ghc
GHC_OPTS = -package mtl

BIBTEX=bibtex
BIB=lib

TARFILES = ./$(BIB).bib ./$(MAIN).lhs ./makefile 

.PHONY: all paper quick pdf pdf2 test \ 
	james tex dvi dvi2 bib code touch \ 
	clean cleaner cleanest tar

all : 	james # exchange this for 'paper' for the Gundry version

james : bib dvi2 $(MAIN).pdf touch 
	

paper : $(MAIN).tex $(BIB).bib pdf bib pdf2 touch 
	

quick : $(MAIN).tex pdf touch 
	

pdf : 
	@ $(PDF) 

pdf2 : 
	@ $(PDF)   
	@ if egrep Rerun $(MAIN).log; then $(PDF); fi 

test :  $(MAIN).lhs
	$(GHC) $(GHC_OPTS) $< -o $(MAIN) 
	./$(MAIN) 

dvi : $(MAIN).dvi 
	

bib : $(MAIN).bbl 
	

tex : $(MAIN).tex 
	

dvi2 : 
	@ $(DVI) 
	@ if egrep Rerun $(MAIN).log; then $(DVI) ; fi 

code : $(MAIN).hs 
	

touch : 
	@ touch $(MAIN).tex

$(MAIN).pdf: $(MAIN).dvi $(MAIN).bbl 
	@ $(DVIPS) $< | $(PS2PDF) $@ 

$(MAIN).bbl: $(BIB).bib $(MAIN).dvi  
	@ $(BIBTEX) $(MAIN)

$(MAIN).dvi: $(MAIN).tex 
	@ $(DVI) 

$(MAIN).tex: $(MAIN).lhs 
	@ $(LHS2TEX) $(LHS2TEX_OPTS) $< -o $@  

$(MAIN).hs: $(MAIN).lhs 
	@ $(LHS2TEX) --newcode $< -o $@  

clean : 
	@ -rm *.aux *.log *.blg

cleaner : clean 
	@ -rm *.dvi *.ptb *.out *.bbl 

cleanest : clean cleaner
	@ -rm *.hs $(MAIN).pdf 

tar : 	$(MAIN).tgz 
	

$(MAIN).tgz: $(TARFILES) 
	tar cvfz /tmp/$@ $(TARFILES) 
