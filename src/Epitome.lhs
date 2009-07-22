%if False

> module Epitome where

%endif

\documentclass[a4paper]{report}
\usepackage{stmaryrd,wasysym,url,upgreek,palatino,alltt}

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
%include Rules.lhs
%include Core.lhs

\chapter{Feature by Feature}

%include Features.lhs
%include UId.lhs
%include Enum.lhs
%include Sigma.lhs
%include Prop.lhs

\chapter{Concrete Syntax}

%include Lexer.lhs
%include Layout.lhs
%include TmParse.lhs

\chapter{Compiler}

%include Compiler.lhs

\end{document}