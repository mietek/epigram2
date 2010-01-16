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
\usepackage{bussproofs}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%include stuff.fmt

\input{Documentation/Macros.tex}

\begin{document}

\title{An Epigram Implementation}
\author{Edwin Brady,  James Chapman, Pierre-\'{E}variste Dagand, \\
   Adam Gundry, Conor McBride, Peter Morris, Ulf Norell
}
\maketitle

\tableofcontents

\chapter{Introduction}

\input{Documentation/Introduction.tex}

\input{Documentation/Language.tex}

\chapter{The Name Supply}

\input{NameSupply/Introduction.tex}

%include NameSupply/Root.lhs
%include NameSupply/Rooty.lhs

\chapter{The Evidence Language}

\input{Evidences/Introduction.tex}

%include Evidences/Tm.lhs
%include Evidences/Rules.lhs
%include Evidences/Tactics.lhs

\chapter{Feature by Feature}

\input{Features/Introduction.tex}

%include Features/Features.lhs
%include Features/Skeleton.lhs
%include Features/UId.lhs
%include Features/Enum.lhs
%include Features/Sigma.lhs
%include Features/Prop.lhs
%include Features/Desc.lhs
%include Features/Equality.lhs
%include Features/Labelled.lhs

\chapter{The Proof State}

\input{ProofState/Introduction.tex}

%include ProofState/Developments.lhs
%include ProofState/ProofState.lhs
%include ProofState/Elimination.lhs

\chapter{The Display Language}

\input{DisplayLang/Introduction.tex}

%include DisplayLang/DisplayTm.lhs
%include DisplayLang/Lexer.lhs
%include DisplayLang/Naming.lhs
%include DisplayLang/TmParse.lhs
%include DisplayLang/PrettyPrint.lhs
%include DisplayLang/Distiller.lhs
%include DisplayLang/Elaborator.lhs

\chapter{Cochon}

\input{Cochon/Introduction.tex}

%include Cochon/DevLoad.lhs
%include Cochon/DisplayCommands.lhs
%include Cochon/Cochon.lhs
%include Main.lhs

\chapter{Compiler}

\input{Compiler/Introduction.tex}

%include Compiler/Compiler.lhs

\appendix

\chapter{Kit}

%include Kit/BwdFwd.lhs
%include Kit/Parsley.lhs
%include Kit/MissingLibrary.lhs


\cleardoublepage
\phantomsection
\addcontentsline{toc}{chapter}{Bibliography}
\bibliographystyle{plain}
\bibliography{Epitome}


\end{document}