\section{Skeleton feature}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Skeleton where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanConstructors where

> import -> CanPretty where

> import -> CanTyRules where

> import -> CanCompile where

> import -> EtaExpand where

> import -> CanPats where

> import -> DisplayCanPats where

> import -> TraverseCan where

> import -> HalfZipCan where

\subsection{Plugging Eliminators in}

> import -> ElimTyRules where

> import -> ElimComputation where

> import -> ElimCompile where

> import -> TraverseElim where

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

> import -> ElaborateRules where
 
> import -> DistillRules where

> import -> InDTmConstructors where

> import -> InDTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where

\subsection{Extending the Mangler}

> import -> DMangleRules where

\subsection{Extending the Term Builder}

> import -> SugarTactics where
