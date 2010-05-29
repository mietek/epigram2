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

> import Kit.MissingLibrary

> import Features.Features ()

> import Evidences.Tm
> import Evidences.Mangler

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
reference in |primitives| (Section \ref{subsec:operators})
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
>     DType  :: DInTm p x        -> DHead  p x -- type cast
>     DTEx   :: ExTmWrap p x     -> DHead  p x -- embedding
>  deriving (Functor, Foldable, Traversable, Show)

Note that, again, we are polymorphic in the representation of free
variables. While we reuse the |Can| and |Elim| functors from |Tm|, we
redefine the notion of scope.


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
|Ex| display terms, respectively. This is useful for elaboration, but such terms
cannot be pretty-printed. To make |deriving Traversable| work properly, we have
to |newtype|-wrap them and give trivial |Traversable| instances for the wrappers
manually.

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

%endif


\subsubsection{Type casts}

Because type ascriptions are horrible things to parse, in the display language
we use type casts instead. The type cast |DType ty| gets elaborated to the
identity function for type |ty|, thereby pushing the type into its argument.
The distiller removes type ascriptions and replaces them with appropriate
type casts if necessary.


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

> type InTmRN = InTm RelName
> type ExTmRN = ExTm RelName
> type DInTmRN = DInTm REF RelName
> type DExTmRN = DExTm REF RelName
> type DSPINE = DSpine REF RelName
> type DHEAD = DHead REF RelName
> type DSCOPE = DScope REF RelName

\subsection{Term Construction} 

> dfortran :: DInTm p x -> String
> dfortran (DL (x ::. _)) | not (null x) = x
> dfortran _ = "x"


\subsection{Schemes}

A definition may have a |Scheme|, which allows us to handle implicit syntax.
A |Scheme| is either a type, an explicit $\Pi$ whose domain and codomain are
schemes, or an implicit $\Pi$ whose domain is a type and whose codomain is
a scheme. A |Scheme| is a functor, parameterised by the representation of
types it uses.

> data Scheme x  =  SchType x
>                |  SchExplicitPi (String :<: Scheme x) (Scheme x)
>                |  SchImplicitPi (String :<: x) (Scheme x)
>   deriving Show

%if False

> instance Functor Scheme where
>     fmap = fmapDefault

> instance Foldable Scheme where
>     foldMap = foldMapDefault

> instance Traversable Scheme where
>     traverse f (SchType t) = (|SchType (f t)|)
>     traverse f (SchExplicitPi (x :<: schS) schT) =
>         (| SchExplicitPi (| (x :<:) (traverse f schS) |) (traverse f schT) |)
>     traverse f (SchImplicitPi (x :<: s) schT) = 
>         (| SchImplicitPi (| (x :<:) (f s) |) (traverse f schT) |)

%endif

Given a scheme, we can extract the names of its $\Pi$s:

> schemeNames :: Scheme x -> [String]
> schemeNames (SchType _) = []
> schemeNames (SchExplicitPi (x :<: _) sch) = x : schemeNames sch
> schemeNames (SchImplicitPi (x :<: _) sch) = x : schemeNames sch

We can also convert a |Scheme x| to an |x|, if we are given a way to
interpret $\Pi$-bindings:

> schemeToType :: (String -> x -> x -> x) -> Scheme x -> x
> schemeToType _ (SchType ty) = ty
> schemeToType piv (SchExplicitPi (x :<: s) t) = 
>     piv x (schemeToType piv s) (schemeToType piv t)
> schemeToType piv (SchImplicitPi (x :<: s) t) =
>     piv x s (schemeToType piv t)

> schemeToInTm :: Scheme (InTm x) -> InTm x
> schemeToInTm = schemeToType PIV

> schemeToDInTm :: Scheme (DInTm p x) -> DInTm p x
> schemeToDInTm = schemeToType DPIV


Schemes are stored fully $\lambda$-lifted, so we may need to apply them to a spine
of shared parameters:

> applyScheme :: Scheme INTM -> Spine {TT} REF -> Scheme INTM
> applyScheme sch [] = sch
> applyScheme (SchExplicitPi (x :<: SchType s) schT) (A (NP r) : rs) =
>     applyScheme (underScheme 0 r schT) rs
>   where
>     underScheme :: Int -> REF -> Scheme INTM -> Scheme INTM
>     underScheme n r (SchType ty) = SchType (under n r %% ty)
>     underScheme n r (SchExplicitPi (x :<: schS) schT) =
>         SchExplicitPi (x :<: underScheme n r schS) (underScheme (n+1) r schT)
>     underScheme n r (SchImplicitPi (x :<: s) schT) =
>         SchImplicitPi (x :<: under n r %% s) (underScheme (n+1) r schT)


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


\subsection{Names}

For display and storage purposes, we have a system of local longnames for referring to entries.
Any component of a local name may have a \textasciicircum|n| or |_n| suffix, where |n| is
an integer, representing a relative or absolute offset. A relative
offset \textasciicircum|n| refers to the $n^\mathrm{th}$ occurrence of the name
encountered when searching upwards, so |x|\textasciicircum|0| refers to the same reference
as |x|, but |x|\textasciicircum|1| skips past it and refers to the next thing named |x|.
An absolute offset |_n|, by contrast, refers to the exact numerical
component of the name. 

> data Offs = Rel Int | Abs Int deriving (Show, Eq)
> type RelName = [(String,Offs)]
