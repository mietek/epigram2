%if False

> module DisplayLang.Introduction where

%endif

The life cycle of a term in the system looks like this, where vertices are
labelled with the type of a representation, and edges are labelled with the
transformation between representations.

%% TODO: Rewrite this diagram in Tikz or equivalent

\begin{verbatim}
            Lexer             Parser            Elaborator
   String ---------> [Token] ---------> InDTmRN ----------> INTM
     ^                                                       |
     |                                                       |
     |  Renderer         Pretty-printer           Distiller  |
     +-------------- Doc <------------- InDTmRN <------------+
\end{verbatim}

In the beginning was the |String|. This gets lexed (section \ref{sec:lexer})
to produce a list of |Token|s, which are parsed (section \ref{sec:parser}) to
give an |InDTm RelName| (a term in the display syntax containing relative
names). The display term is then elaborated (section \ref{sec:elaborator})
in the |ProofState| monad to produce an |INTM| (a term in the evidence
language).

Reversing the process, the distiller (section \ref{sec:distiller}) converts
an evidence term back to a display term, and the pretty-printer
(section \ref{sec:pretty_printer}) renders this as a |String|.

%% TODO: this diagram ought to be quickchecked