HC      = ghc

SRCS = Main.lhs Tm.lhs Sigma.lhs BwdFwd.lhs 
OBJS = Main.o Tm.o Sigma.o BwdFwd.o 

.SUFFIXES : .o .hs .hi .lhs .hc .s

Pig : $(OBJS)
	rm -f $@
	$(HC) -o $@ $(HC_OPTS) $(OBJS)

.depend : $(SRCS)
	ghc -M -dep-makefile .depend Main.lhs

dvi : Epitome.dvi

Epitome.dvi : Epitome.tex
	latex Epitome

Epitome.tex : Epitome.lhs Lexer.lhs Layout.lhs BwdFwd.lhs Parsley.lhs Root.lhs Features.lhs Tm.lhs TmParse.lhs stuff.fmt
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

include .depend

