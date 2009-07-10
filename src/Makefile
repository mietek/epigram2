dvi : Epitome.dvi

Epitome.dvi : Epitome.tex
	latex Epitome

Epitome.tex : Epitome.lhs Lexer.lhs Layout.lhs BwdFwd.lhs stuff.fmt
	lhs2TeX --poly Epitome.lhs > Epitome.tex
