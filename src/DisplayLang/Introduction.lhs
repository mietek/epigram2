%if False

> module DisplayLang.Introduction where

%endif

The life cycle of a term in the system looks like this, where vertices are
labelled with the type of a representation, and edges are labelled with the
transformation between representations.

%% TODO: Rewrite this diagram in Tikz or equivalent

\begin{verbatim}
            Lexer             Parser            Elaborator
   String ---------> [Token] ---------> DInTmRN ----------> INTM
     ^                                                       |
     |                                                       |
     |  Renderer         Pretty-printer           Distiller  |
     +-------------- Doc <------------- DInTmRN <------------+
\end{verbatim}

In the beginning was the |String|. This gets lexed (section
\ref{sec:DisplayLang.Lexer}) to produce a list of |Token|s, which are
parsed (section \ref{sec:DisplayLang.TmParse}) to give an |DInTm
RelName| (a term in the display syntax containing relative names). The
display term is then elaborated (section
\ref{sec:Elaborator.Elaborator}) in the |ProofState| monad to produce
an |INTM| (a term in the evidence language).

Reversing the process, the distiller (section
\ref{sec:Distillation.Distiller}) converts an evidence term back to a
display term, and the pretty-printer (section
\ref{sec:DisplayLang.PrettyPrint}) renders this as a |String|.

%% TODO: this diagram ought to be quickchecked