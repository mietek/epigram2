\section{Skeleton feature}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Skeleton where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanConstructors where

> import -> CanTyRules where

> import -> CanCompile where

> import -> CanEtaExpand where

> import -> CanPats where

> import -> CanDisplayPats where

> import -> CanPretty where

> import -> CanTraverse where

> import -> CanHalfZip where

\subsection{Plugging Eliminators in}

> import -> ElimTyRules where

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

\subsection{Plugging Operators in}

> import -> Operators where

> import -> OpCompile where

> import -> OpCode where

\subsection{Plugging Axioms in}

> import -> Axioms where

> import -> AxCode where

\subsection{Extending the type-checker}

> import -> Check where

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where

\subsection{Extending the quotient}

> import -> QuotientDefinitions where

\subsection{Extending the Display Language}

> import -> MakeElabRules where
 
> import -> DistillRules where

> import -> InDTmConstructors where

> import -> InDTmTraverse where

> import -> InDTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where