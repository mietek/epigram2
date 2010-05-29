\section{Skeleton feature}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Skeleton where

%endif


\subsection{Plugging in canonical forms}

> import -> CanConstructors where

> import -> CanTyRules where

> import -> CanCompile where

> import -> CanEtaExpand where

> import -> CanPats where

> import -> CanDisplayPats where

> import -> CanPretty where

> import -> CanTraverse where

> import -> CanHalfZip where

\subsection{Plugging in eliminators}

> import -> ElimTyRules where

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

\subsection{Plugging in operators}

> import -> Operators where

> import -> OpCompile where

> import -> OpCode where

\subsection{Plugging in axioms and primitives}

> import -> RulesCode where

> import -> Primitives where

\subsection{Extending the type-checker}

> import -> Check where

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where

\subsection{Extending the display language}

> import -> DInTmConstructors where

> import -> DInTmTraverse where

> import -> DInTmPretty where

> import -> Pretty where

\subsection{Extending the concrete syntax}

> import -> KeywordConstructors where

> import -> KeywordTable where

> import -> ElimParsers where

> import -> DInTmParsersSpecial where

> import -> DInTmParsersMore where

> import -> ParserCode where

\subsection{Extending the elaborator and distiller}

> import -> MakeElabRules where
 
> import -> DistillRules where