\section{Display Terms}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
>     ScopedTypeVariables,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module DisplayLang.DisplayTm where

> import Control.Applicative
> import Data.Foldable hiding (foldl)
> import Data.Traversable

> import Features.Features ()

> import Evidences.Tm

> import Kit.MissingLibrary

%endif

%format ::$ = ":\!\!:\!\!\$"
%format ::. = ":\!\bullet"

\subsection{Structure of Display Terms}

Display terms mirror and extend the |Tm {d, TT}| terms of the Evidence
language. While the Evidence language is the language of the
type-checker, the Display language is the one of humans in an
interactive development. Hence, in addition to the terms from the
Evidence language, we have the following:

\begin{itemize} 

\item Question marks (holes), which are turned into subgoals during elaboration
      (Chapter \ref{chap:elaboration}) ;
\item Underscores (jokers), which are inferred during elaboration ;
\item Embedding of evidence terms into display terms ;
\item Type annotations ; and
\item Feature-specific extensions, which are imported from an aspect.
\end{itemize}

However, we have removed the following:
\begin{itemize}
\item Type ascriptions, replaced by type annotations ; and
\item Operators, replaced by a parameter containing the corresponding
reference in |primitives| (Section \ref{sec:Evidences.Operators})
\end{itemize}


\begin{danger}

Because of a limitation of GHC |deriving Traversable|, we define two
mutually recursive data types instead of taking a |Dir|
parameter. Thanks to this hack, we can use |deriving Traversable|.

\end{danger}

> data DInTm :: * -> * -> * where
>     DL     :: DScope p x       ->  DInTm p x -- \(\lambda\)
>     DC     :: Can (DInTm p x)  ->  DInTm p x -- canonical
>     DN     :: DExTm p x        ->  DInTm p x -- neutral
>     DQ     :: String           ->  DInTm p x -- hole
>     DU     ::                      DInTm p x -- underscore
>     DT     :: InTmWrap p x     ->  DInTm p x -- embedding
>     import <- DInTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)
>
> data DExTm p x = DHead p x ::$ DSpine p x
>   deriving (Functor, Foldable, Traversable, Show)
>
> data DHead :: * -> * -> * where
>     DP     :: x                -> DHead  p x -- parameter
>     DType  :: DInTm p x        -> DHead  p x -- type annotation
>     DTEx   :: ExTmWrap p x     -> DHead  p x -- embedding
>  deriving (Functor, Foldable, Traversable, Show)

Note that, again, we are polymorphic in the representation of free
variables. The variables in Display terms are denoted here by |x|.
The variables of embedded Evidence terms are denoted by |p|. Hence,
there is two potentially distinct set of free variables.

While we reuse the |Can| and |Elim| functors from |Tm|, we redefine
the notion of scope. We store |DExTm|s so as to give easy access to
the head and spine for elaboration and pretty-printing.


%if False

> dfortran :: DInTm p x -> String
> dfortran (DL (x ::. _)) | not (null x) = x
> dfortran _ = "x"

%endif

\subsubsection{Scopes, canonical objects and eliminators}


The |DScope| functor is a simpler version of the |Scope| functor: we
only ever consider \emph{terms} here, while |Scope| had to deal with
\emph{values}. Hence, we give this purely syntaxic, first-order
representation of scopes:

> data DScope :: * -> * -> * where
>     (::.)  :: String -> DInTm p x  -> DScope p x  -- binding
>     DK     :: DInTm p x            -> DScope p x  -- constant
>   deriving (Functor, Foldable, Traversable, Show)

We provide handy projection functions to get the name and body of a scope:

> dScopeName :: DScope p x -> String
> dScopeName (x ::. _)  = x
> dScopeName (DK _)     = "_"

> dScopeTm :: DScope p x -> DInTm p x
> dScopeTm (_ ::. tm)  = tm
> dScopeTm (DK tm)     = tm

Spines of eliminators are just like in the evidence language:

> type DSpine p x = [Elim (DInTm p x)]

> ($::$) :: DExTm p x -> Elim (DInTm p x) -> DExTm p x
> (h ::$ s) $::$ a = h ::$ (s ++ [a])


\subsubsection{Embedding evidence terms}

The |DT| and |DTEx| constructors allow evidence terms to be treated as |In| and
|Ex| display terms, respectively. This is useful for elaboration, because it
allows the elaborator to combine finished terms with display syntax and
continue elaborating. Such terms cannot be pretty-printed, however, so they
should not be used in the distiller.

\begin{danger}

To make |deriving Traversable| work properly, we have to
|newtype|-wrap them and manually give trivial |Traversable| instances
for the wrappers. The instantiation code is hidden in the literate
document.

\end{danger}

> newtype InTmWrap  p x = InTmWrap  (InTm p)  deriving Show
> newtype ExTmWrap  p x = ExTmWrap  (ExTm p)  deriving Show

> pattern DTIN x = DT (InTmWrap x)
> pattern DTEX x = DTEx (ExTmWrap x)

%if False

> instance Functor (InTmWrap p) where
>   fmap = fmapDefault
> instance Foldable (InTmWrap p) where
>   foldMap = foldMapDefault
> instance Traversable (InTmWrap p) where
>   traverse f (InTmWrap x) = pure (InTmWrap x)

> instance Functor (ExTmWrap p) where
>   fmap = fmapDefault
> instance Foldable (ExTmWrap p) where
>   foldMap = foldMapDefault
> instance Traversable (ExTmWrap p) where
>   traverse f (ExTmWrap x) = pure (ExTmWrap x)

The following are essentially saying that |DInTm| is traversable in its first
argument, as well as its second.

> traverseDTIN :: Applicative f => (p -> f q) -> DInTm p x -> f (DInTm q x)
> traverseDTIN f (DL (x ::. tm)) = (|DL (|(x ::.) (traverseDTIN f tm)|)|)
> traverseDTIN f (DL (DK tm)) = (|DL (|DK (traverseDTIN f tm)|)|)
> traverseDTIN f (DC c) = (|DC (traverse (traverseDTIN f) c)|)
> traverseDTIN f (DN n) = (|DN (traverseDTEX f n)|)
> traverseDTIN f (DQ s) = (|(DQ s)|)
> traverseDTIN f DU     = (|DU|)
> traverseDTIN f (DTIN tm) = (|DTIN (traverse f tm)|)
> import <- DInTmTraverse

> traverseDTEX :: Applicative f => (p -> f q) -> DExTm p x -> f (DExTm q x)
> traverseDTEX f (h ::$ as) = (|(traverseDHead f h) ::$ (traverse (traverse (traverseDTIN f)) as)|)

> traverseDHead :: Applicative f => (p -> f q) -> DHead p x -> f (DHead q x)
> traverseDHead f (DP x) = (|(DP x)|)
> traverseDHead f (DType tm) = (|DType (traverseDTIN f tm)|)
> traverseDHead f (DTEX tm) = (|DTEX (traverse f tm)|)


%endif


\subsubsection{Type annotations}

Because type ascriptions are horrible things to parse\footnote{Left
nesting is not really a friend of our damn parser}, in the display
language we use type annotations instead. The type annotation |DType
ty| gets elaborated to the identity function for type |ty|, thereby
pushing the type into its argument.  The distiller removes type
ascriptions and replaces them with appropriate type annotations if
necessary.


\subsection{Useful Abbreviations}

The convention for display term pattern synonyms is that they should match
their evidence term counterparts, but with the addition of |D|s in appropriate
places.

> pattern DSET        = DC Set              
> pattern DARR s t    = DPI s (DL (DK t)) 
> pattern DPI s t     = DC (Pi s t)         
> pattern DCON t      = DC (Con t)
> pattern DNP n       = DN (DP n ::$ [])
> pattern DLAV x t    = DL (x ::. t)
> pattern DPIV x s t  = DPI s (DLAV x t)
> pattern DLK t       = DL (DK t)
> pattern DTY ty tm   = DType ty ::$ [A tm]
> import <- CanDisplayPats


\subsection{Sizes}

We keep track of the |Size| of terms when parsing, to avoid nasty left
recursion, and when pretty-printing, to minimise the number of brackets we
output. In increasing order, the sizes are:

> data Size = ArgSize | AppSize | EqSize | AndSize | ArrSize | PiSize
>   deriving (Show, Eq, Enum, Bounded, Ord)

When a higher-size term has to be put in a lower-size position, it must
be wrapped in parentheses. For example, an application has |AppSize| but its
arguments have |ArgSize|, so |g (f x)| cannot be written |g f x|, whereas
|EqSize| is bigger than |AppSize| so |f x == g x| means the same thing as
|(f x) == (g x)|.


