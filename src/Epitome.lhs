%if False

> module Epitome where

%endif

\documentclass[a4paper]{report}
\usepackage{stmaryrd,wasysym,url,
            upgreek,palatino,alltt,
            color}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%include stuff.fmt

\begin{document}

\title{An Epigram Implementation}
\author{Conor McBride, James Chapman, Peter Morris, Edwin Brady}
\maketitle

\chapter{Perversity}

%include BwdFwd.lhs
%include Parsley.lhs

\chapter{Core}

%include Root.lhs
%include Tm.lhs
%include Tactics.lhs
%include Rules.lhs
%include Developments.lhs
%include DevLoad.lhs
%include Construction.lhs

\chapter{Feature by Feature}

%include Features.lhs
%include UId.lhs
%include Enum.lhs
%include Sigma.lhs
%include Prop.lhs
%include Containers.lhs

\chapter{Concrete Syntax}

%include Lexer.lhs
%include Layout.lhs
%include TmParse.lhs

\chapter{Compiler}

%include Compiler.lhs

\chapter{Elaborator}

%include Elaborator.lhs


\bibliographystyle{plain}
\bibliography{Epitome}


\end{document}