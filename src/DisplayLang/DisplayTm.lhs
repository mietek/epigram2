\section{DisplayTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
>     ScopedTypeVariables,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module DisplayLang.DisplayTm where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable hiding (foldl)
> import Data.Traversable

> import Kit.MissingLibrary

> import Features.Features

> import Evidences.Tm

%endif

%format ::$ = ":\!\!:\!\!\$"
%format ::. = ":\!\bullet"

\subsection{The Life Cycle of a Term}

The life cycle of a term in the system looks like this, where vertices are
labelled with the type of a representation, and edges are labelled with the
transformation between representations.

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


\subsection{Structure of Display Terms}

Display terms correspond roughly to |Tm {d, TT}| in the evidence language, but
instead of taking a |Dir| parameter, we define two mutually recursive data
types. This allows us to use |deriving Traversable|. Again, they are polymorphic
in the representation of free variables. In addition to the structures from
the evidence language, we have the following:
\begin{itemize}
\item Question marks (holes) which are replaced by subgoals on elaboration.
\item Underscores which are determined by the typing rules on elaboration.
\item Embedding of evidence terms into display terms.
\item Type casts.
\item Extensions imported from an aspect.
\end{itemize}

However, we have removed the following:
\begin{itemize}
\item Type ascriptions (use type casts instead).
\item Operators (use parameters with appropriate references instead).
\end{itemize}

> data InDTm :: * -> * where
>     DL     :: DScope x                   -> InDTm  x -- \(\lambda\)
>     DC     :: Can (InDTm x)              -> InDTm  x -- canonical
>     DN     :: ExDTm x                    -> InDTm  x -- neutral
>     DQ     :: String                     -> InDTm  x -- hole
>     DU     ::                               InDTm  x -- underscore
>     DT     :: InTmWrap x                 -> InDTm  x -- embedding
>     import <- InDTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)

> data ExDTm :: * -> * where
>     DP     :: x                          -> ExDTm  x -- parameter
>     DV     :: Int                        -> ExDTm  x -- variable
>     (::$)  :: ExDTm x -> Elim (InDTm x)  -> ExDTm  x -- elim
>     DType  :: InDTm x                    -> ExDTm  x -- type cast
>     DTEx   :: ExTmWrap x                 -> ExDTm  x -- embedding
>     import <- ExDTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)


\subsubsection{Scopes, canonical objects and eliminators}

Note that we reuse the |Can| and |Elim| functors from |Tm|.

The |DScope| functor is a simpler version of the |Scope| functor because it
doesn't need to deal with the |VV| phase.

> data DScope :: * -> * where
>     (::.)  :: String -> InDTm x          -> DScope x  -- binding
>     DK     :: InDTm x                    -> DScope x  -- constant
>   deriving (Functor, Foldable, Traversable, Show)

We provide handy projection functions to get the name and body of a scope:

> dScopeName :: DScope x -> String
> dScopeName (x ::. _)  = x
> dScopeName (DK _)     = "_"

> dScopeTm :: DScope x -> InDTm x
> dScopeTm (_ ::. tm)  = tm
> dScopeTm (DK tm)     = tm

Spines of eliminators are just like in the evidence language:

> type DSpine x = [Elim (InDTm x)]
>
> ($::$) :: ExDTm x -> DSpine x -> ExDTm x
> ($::$) = foldl (::$)


\subsubsection{Embedding evidence terms}

The |DT| and |DTEx| constructors allow evidence terms to be treated as |In| and
|Ex| display terms, respectively. This is useful for elaboration, but such terms
cannot be pretty-printed. To make |deriving Traversable| work properly, we have
to |newtype|-wrap them and give trivial |Traversable| instances for the wrappers
manually.

> newtype InTmWrap  x = InTmWrap  INTM  deriving Show
> newtype ExTmWrap  x = ExTmWrap  EXTM  deriving Show

%if False

> instance Functor InTmWrap where
>   fmap = fmapDefault
> instance Foldable InTmWrap where
>   foldMap = foldMapDefault
> instance Traversable InTmWrap where
>   traverse f (InTmWrap x) = pure (InTmWrap x)

> instance Functor ExTmWrap where
>   fmap = fmapDefault
> instance Foldable ExTmWrap where
>   foldMap = foldMapDefault
> instance Traversable ExTmWrap where
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
> pattern DNV n       = DN (DV n)
> pattern DNP n       = DN (DP n)
> pattern DLAV x t    = DL (x ::. t)
> pattern DPIV x s t  = DPI s (DLAV x t)
> pattern DLK t       = DL (DK t)
> pattern DTY ty tm   = (DType ty) ::$ A tm
> import <- CanDisplayPats

We need fewer type synoyms:

> type INDTM  = InDTm REF 
> type EXDTM  = ExDTm REF


\subsection{Term Construction} 

> dfortran :: InDTm x -> String
> dfortran (DL (x ::. _)) | not (null x) = x
> dfortran _ = "x"


\subsection{Schemes}

> schemeToInDTm :: Scheme (InDTm x) -> InDTm x
> schemeToInDTm (SchType ty) = ty
> schemeToInDTm (SchExplicitPi (x :<: s) t) = DPIV x (schemeToInDTm s) (schemeToInDTm t)
> schemeToInDTm (SchImplicitPi (x :<: s) t) = DPIV x s (schemeToInDTm t)


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