HC      = ghc

SRCS = Epitome.lhs Main.lhs Rules.lhs Tm.lhs Sigma.lhs Features.lhs BwdFwd.lhs Root.lhs\
       Lexer.lhs Layout.lhs Parsley.lhs TmParse.lhs
OBJS = Epitome.o Main.o Rules.o Tm.o Sigma.o Features.o BwdFwd.o Root.o\
       Lexer.o Layout.o Parsley.o TmParse.o

.SUFFIXES : .o .hs .hi .lhs .hc .s

Pig : $(OBJS)
	rm -f $@
	$(HC) -o $@ $(HC_OPTS) $(OBJS)

.depend : $(SRCS)
	ghc -M -dep-makefile .depend Main.lhs

dvi : Epitome.dvi

Epitome.dvi : Epitome.tex
	latex Epitome

Epitome.tex : $(SRCS) stuff.fmt
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

