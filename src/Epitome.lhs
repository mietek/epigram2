%if False

> module Epitome where

%endif

\documentclass[a4paper]{report}
\usepackage{stmaryrd}
\usepackage{wasysym}
\usepackage{url}
\usepackage{upgreek}
\usepackage{palatino}
\usepackage{alltt}
\usepackage{color}
\usepackage{hyperref}
\usepackage{a4wide}
\usepackage{amsthm}
\usepackage{manfnt}
\usepackage{makeidx}
\usepackage{subfigure}

\usepackage{pig}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%include stuff.fmt

\newbox\subfigbox
\makeatletter
\newenvironment{subfloat}
               {\def\caption##1{\gdef\subcapsave{\relax##1}}%
                \let\subcapsave\@@empty
                \setbox\subfigbox\hbox
                \bgroup}
               {\egroup\subfigure[\subcapsave]{\box\subfigbox}}
\makeatother

\input{Documentation/Macros.tex}

\makeindex

\begin{document}

\ColourEpigram

\title{An Epigram Implementation}
\author{Edwin Brady,  James Chapman, Pierre-\'{E}variste Dagand, \\
   Adam Gundry, Conor McBride, Peter Morris, Ulf Norell, Nicolas Oury
}
\maketitle

\tableofcontents

\chapter{Introduction}

\input{Documentation/Introduction.tex}

\input{Documentation/Language.tex}

\chapter{The Evidence Language}

\input{Evidences/Introduction.tex}

%include Evidences/Tm.lhs
%include Evidences/NameSupply.lhs
%include Evidences/TypeChecker.lhs
%include Evidences/TypeCheckRules.lhs
%include Evidences/EtaQuote.lhs
%include Evidences/DefinitionalEquality.lhs
%include Evidences/ErrorHandling.lhs
%include Evidences/News.lhs

\chapter{The Display Language}

%include DisplayLang/Introduction.lhs

%include DisplayLang/DisplayTm.lhs
%include DisplayLang/Name.lhs
%include DisplayLang/Scheme.lhs
%include DisplayLang/Lexer.lhs
%include DisplayLang/TmParse.lhs
%include DisplayLang/PrettyPrint.lhs

\chapter{The Proof State}

\input{ProofState/Introduction.tex}

%include ProofState/Structure.lhs
%include ProofState/ProofContext.lhs
%include ProofState/GetSet.lhs
%include ProofState/Navigation.lhs
%include ProofState/Interface.lhs
%include ProofState/NameResolution.lhs

\chapter{The Proof Tactics}

\input{Tactics/Introduction.tex}

%include Tactics/Information.lhs
% %include Tactics/Elimination.lhs
%include Tactics/PropositionSimplify.lhs
% %include Tactics/ProblemSimplify.lhs
% %include Tactics/Record.lhs
% %include Tactics/Relabel.lhs
% %include Tactics/Gadgets.lhs
% %include Tactics/ShowHaskell.lhs
%include Tactics/Unification.lhs
%include Tactics/Matching.lhs

\chapter{Elaboration}
\label{chap:elaboration}

%include Elaboration/ElabProb.lhs
%include Elaboration/ElabMonad.lhs
%include Elaboration/MakeElab.lhs
%include Elaboration/RunElab.lhs
%include Elaboration/Elaborator.lhs
%include Elaboration/Scheduler.lhs
%include Elaboration/Wire.lhs

\chapter{Distillation}

%include Distillation/Distiller.lhs
%include Distillation/Scheme.lhs
%include Distillation/Moonshine.lhs

\chapter{Cochon}

\input{Cochon/Introduction.tex}

%include Cochon/CommandLexer.lhs
%include Cochon/Cochon.lhs
%include Cochon/Error.lhs
%include Main.lhs

\chapter{The Source Language}

%include SourceLang/Structure.lhs
%include SourceLang/Parser.lhs
%include SourceLang/Elaborator.lhs
%include SourceLang/Example.lhs

\chapter{Compiler}

\input{Compiler/Introduction.tex}

% %include Compiler/Compiler.lhs

\appendix

\chapter{Kit}

%include Kit/BwdFwd.lhs
%include Kit/NatFinVec.lhs
%include Kit/Parsley.lhs
%include Kit/MissingLibrary.lhs
%include Kit/Trace.lhs

\cleardoublepage
\phantomsection
\addcontentsline{toc}{chapter}{Bibliography}
\bibliographystyle{plain}
\bibliography{Epitome}

\cleardoublepage
\phantomsection
\addcontentsline{toc}{chapter}{Index}
\printindex

\end{document}
