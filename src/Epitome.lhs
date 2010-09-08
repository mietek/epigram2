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

\chapter{The Name Supply}

\input{NameSupply/Introduction.tex}

%include NameSupply/NameSupply.lhs
%include NameSupply/NameSupplier.lhs

\chapter{The Evidence Language}

\input{Evidences/Introduction.tex}

%include Evidences/Tm.lhs
%include Evidences/Mangler.lhs
%include Evidences/Eval.lhs
%include Evidences/TypeChecker.lhs
%include Evidences/DefinitionalEquality.lhs
%include Evidences/BetaQuotation.lhs
%include Evidences/Operators.lhs
%include Evidences/OperatorDSL.lhs
%include Evidences/PropositionalEquality.lhs
%include Evidences/Utilities.lhs

\chapter{The Display Language}

%include DisplayLang/Introduction.lhs

%include DisplayLang/DisplayTm.lhs
%include DisplayLang/Name.lhs
%include DisplayLang/Scheme.lhs
%include DisplayLang/Lexer.lhs
%include DisplayLang/TmParse.lhs
%include DisplayLang/PrettyPrint.lhs

\chapter{Feature by Feature}

\input{Features/Introduction.tex}

%include Features/Features.lhs
%include Features/Skeleton.lhs
%include Features/UId.lhs
%include Features/Enum.lhs
%include Features/Sigma.lhs
%include Features/Prop.lhs
%include Features/Desc.lhs
%include Features/IDesc.lhs
%include Features/Equality.lhs
%include Features/FreeMonad.lhs
%include Features/Nu.lhs
%include Features/Labelled.lhs
%include Features/Quotient.lhs
%include Features/Record.lhs
%include Features/Anchor.lhs

\chapter{The Proof State}

\input{ProofState/Introduction.tex}

%include ProofState/Structure/Developments.lhs
%include ProofState/Structure/Entries.lhs

%include ProofState/Edition/News.lhs
%include ProofState/Edition/ProofContext.lhs
%include ProofState/Edition/ProofState.lhs
%include ProofState/Edition/Entries.lhs
%include ProofState/Edition/FakeRef.lhs
%include ProofState/Edition/Scope.lhs
%include ProofState/Edition/GetSet.lhs
%include ProofState/Edition/Navigation.lhs

%include ProofState/Interface/ProofKit.lhs
%include ProofState/Interface/Name.lhs
%include ProofState/Interface/Parameter.lhs
%include ProofState/Interface/Definition.lhs
%include ProofState/Interface/Module.lhs
%include ProofState/Interface/Search.lhs
%include ProofState/Interface/Solving.lhs
%include ProofState/Interface/NameResolution.lhs
%include ProofState/Interface/Lifting.lhs
%include ProofState/Interface/Anchor.lhs

\chapter{The Proof Tactics}

\input{Tactics/Introduction.tex}

%include Tactics/Information.lhs
%include Tactics/Elimination.lhs
%include Tactics/PropositionSimplify.lhs
%include Tactics/ProblemSimplify.lhs
%include Tactics/Data.lhs
%include Tactics/Record.lhs
%include Tactics/Relabel.lhs
%include Tactics/Gadgets.lhs
%include Tactics/ShowHaskell.lhs
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

%include Cochon/DevLoad.lhs
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

%include Compiler/OpDef.lhs
%include Compiler/Compiler.lhs

\appendix

\chapter{Kit}

%include Kit/BwdFwd.lhs
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