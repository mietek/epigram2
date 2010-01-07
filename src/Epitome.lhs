%if False

> module Epitome where

%endif

\documentclass[a4paper]{report}
\usepackage{stmaryrd,wasysym,url,
            upgreek,palatino,alltt,
            color, bussproofs}
\usepackage{hyperref}
\usepackage{a4wide}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%include stuff.fmt

\begin{document}

\title{An Epigram Implementation}
\author{Edwin Brady,  James Chapman, Pierre-\'{E}variste Dagand, \\
   Adam Gundry, Conor McBride, Peter Morris, Ulf Norell
}
\maketitle

\tableofcontents

\chapter{Introduction}

\input{Docs/Intro.tex}
\input{Docs/Language.tex}

\chapter{Core}
%include Root.lhs
%include Rooty.lhs
%include Tm.lhs
%include Rules.lhs
%include Tactics.lhs
%include Developments.lhs

\chapter{Feature by Feature}
%include Features.lhs
%include UId.lhs
%include Enum.lhs
%include Sigma.lhs
%include Prop.lhs
%include Containers.lhs
%include Desc.lhs
%include Equality.lhs

\chapter{Proof State}
%include ProofState.lhs
%include Elimination.lhs

\chapter{Display Language}
%include DisplayTm.lhs
%include Lexer.lhs
%include Naming.lhs
%include TmParse.lhs
%include DevLoad.lhs
%include PrettyPrint.lhs

\chapter{Cochon}
%include Elaborator.lhs
%include Distiller.lhs
%include DisplayCommands.lhs
%include Cochon.lhs
%include Main.lhs

\chapter{Compiler}
%include Compiler.lhs

\appendix

\chapter{Perversity}
%include BwdFwd.lhs
%include Parsley.lhs
%include MissingLibrary.lhs
%include Nat.lhs

\cleardoublepage
\phantomsection
\addcontentsline{toc}{chapter}{Bibliography}
\bibliographystyle{plain}
\bibliography{Epitome}


\end{document}