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

> import Evidences.Tm

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.NatFinVec

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

> data DInTm :: * -> * where
>     DL     :: DScope x          ->  DInTm x -- \(\lambda\)
>     DC     :: Can -> [DInTm x]  ->  DInTm x -- canonical
>     DN     :: DExTm x           ->  DInTm x -- neutral
>     DQ     :: String            ->  DInTm x -- hole
>     DU     ::                       DInTm x -- underscore
>     DT     :: InTmWrap x        ->  DInTm x -- embedding
>     -- import <- DInTmConstructors
>    
>     -- [Feature = Equality]

In the display syntax, an equality can be between arbitrary DExTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEq|
to DInTm, along with appropriate elaboration and distillation rules.

>     DEq :: DExTm x -> DExTm x -> DInTm x
>     -- [/Feature = Equality]

>     {-
>     -- [Feature = Anchor]
>     DAnchor :: String -> DInTm x -> DInTm x 
>     -- [/Feature = Anchor] 
>     -- [Feature = IDesc]
>     -- DIMu :: Labelled (Id :*: Id) (DInTm p x) -> DInTm p x  -> DInTm p x 
>     -- [/Feature = IDesc]
>     -- [Feature = UId]
>     DTag :: String -> [DInTm x] -> DInTm x
>     -- [/Feature = UId]
>     -}
>  deriving (Functor, Foldable, Traversable, Show)
>
> data DExTm x = DHead x ::$ DSpine x
>   deriving (Functor, Foldable, Traversable, Show)
>
> data DHead :: * -> * where
>     DP     :: x           -> DHead x -- parameter
>     DType  :: DInTm x     -> DHead x -- type annotation
>     DTEx   :: ExTmWrap x  -> DHead x -- embedding
>     -- [Feature = Equality]
>     DRefl  :: DInTm x ->  DInTm x -> DHead x 
>     DCoeh  :: Coeh -> DInTm x ->  DInTm x ->  DInTm x -> DInTm x -> DHead x 
>     -- [/Feature = Equality]
>  deriving (Functor, Foldable, Traversable, Show)

Note that, again, we are polymorphic in the representation of free
variables. The variables in Display terms are denoted here by |x|.
The variables of embedded Evidence terms are denoted by |p|. Hence,
there is two potentially distinct set of free variables.

While we reuse the |Can| and |Elim| functors from |Tm|, we redefine
the notion of scope. We store |DExTm|s so as to give easy access to
the head and spine for elaboration and pretty-printing.


%if False

> dfortran :: DInTm x -> String
> dfortran (DL (x ::. _)) | not (null x) = x
> dfortran _ = "x"

%endif

\subsubsection{Scopes, canonical objects and eliminators}


The |DScope| functor is a simpler version of the |Scope| functor: we
only ever consider \emph{terms} here, while |Scope| had to deal with
\emph{values}. Hence, we give this purely syntaxic, first-order
representation of scopes:

> data DScope :: * -> * where
>     (::.)  :: String -> DInTm x  -> DScope x  -- binding
>     DK     :: DInTm x            -> DScope x  -- constant
>   deriving (Functor, Foldable, Traversable, Show)

We provide handy projection functions to get the name and body of a scope:

> dScopeName :: DScope x -> String
> dScopeName (x ::. _)  = x
> dScopeName (DK _)     = "_"

> dScopeTm :: DScope x -> DInTm x
> dScopeTm (_ ::. tm)  = tm
> dScopeTm (DK tm)     = tm

Spines of eliminators are just like in the evidence language:

> type DSpine x = [Elim (DInTm x)]

> ($::$) :: DExTm x -> Elim (DInTm x) -> DExTm x
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



> newtype InTmWrap  x = InTmWrap  EXP
> newtype ExTmWrap  x = ExTmWrap  EXP

> pattern DTIN x = DT (InTmWrap x)
> pattern DTEX x = DTEx (ExTmWrap x)


> instance Functor InTmWrap where
>   fmap = fmapDefault
> instance Foldable InTmWrap where
>   foldMap = foldMapDefault
> instance Traversable InTmWrap where
>   traverse f (InTmWrap x) = pure (InTmWrap x)
> instance Show (InTmWrap x) where
>   show x = "InTm"

> instance Functor ExTmWrap where
>   fmap = fmapDefault
> instance Foldable ExTmWrap where
>   foldMap = foldMapDefault
> instance Traversable ExTmWrap where
>   traverse f (ExTmWrap x) = pure (ExTmWrap x)
> instance Show (ExTmWrap x) where
>   show x = "ExTm"

The following are essentially saying that |DInTm| is traversable in its first
argument, as well as its second.

> {-

> traverseDTIN :: Applicative f => (p -> f q) -> DInTm p x -> f (DInTm q x)
> traverseDTIN f (DL (x ::. tm)) = (|DL (|(x ::.) (traverseDTIN f tm)|)|)
> traverseDTIN f (DL (DK tm)) = (|DL (|DK (traverseDTIN f tm)|)|)
> traverseDTIN f (DC c) = (|DC (traverse (traverseDTIN f) c)|)
> traverseDTIN f (DN n) = (|DN (traverseDTEX f n)|)
> traverseDTIN f (DQ s) = (|(DQ s)|)
> traverseDTIN f DU     = (|DU|)
> traverseDTIN f (DTIN tm) = (|DTIN (traverse f tm)|)
> -- import <- DInTmTraverse
> -- [Feature = Anchor]
> traverseDTIN f (DAnchor s args) = (|(DAnchor s) (traverseDTIN f args)|)
> -- [/Feature = Anchor]
> -- [Feature = Equality]
> traverseDTIN f (DEqBlue t u) =
>   (| DEqBlue (traverseDTEX f t) (traverseDTEX f u) |)
> -- [/Feature = Equality]
> -- [Feature = IDesc]
> -- traverseDTIN f (DIMu s i) = (|DIMu (traverse (traverseDTIN f) s) (traverseDTIN f i)|)
> -- [/Feature = IDesc]
> -- [Feature = UId]
> traverseDTIN f (DTag s xs) = (|(DTag s) (traverse (traverseDTIN f) xs)|)
> -- [/Feature = UId]

> traverseDTEX :: Applicative f => (p -> f q) -> DExTm p x -> f (DExTm q x)
> traverseDTEX f (h ::$ as) = (|(traverseDHead f h) ::$ (traverse (traverse (traverseDTIN f)) as)|)

> traverseDHead :: Applicative f => (p -> f q) -> DHead p x -> f (DHead q x)
> traverseDHead f (DP x) = (|(DP x)|)
> traverseDHead f (DType tm) = (|DType (traverseDTIN f tm)|)
> traverseDHead f (DTEX tm) = (|DTEX (traverse f tm)|)

> -}


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

> pattern DSET        = DC Set []            
> pattern DARR s t    = DPI s (DL (DK t)) 
> pattern DPI s t     = DC Pi [s, t]
> pattern DCON t      = DC Con [t]
> pattern DNP n       = DN (DP n ::$ [])
> pattern DLAV x t    = DL (x ::. t)
> pattern DPIV x s t  = DPI s (DLAV x t)
> pattern DLK t       = DL (DK t)
> pattern DTY ty tm   = DType ty ::$ [A tm]
> -- [Feature = Prop]
> pattern DPROP        = DC Prop []
> pattern DPRF p       = DC Prf [p]
> pattern DALL p q     = DPI p q
> pattern DIMP p q     = DALL (DPRF p) (DL (DK q))
> pattern DALLV x s p  = DALL s (DLAV x p)
> pattern DAND p q     = DC And [p, q]
> pattern DTRIVIAL     = DC One []
> pattern DABSURD      = DC Zero []
> pattern DINH ty      = DC Inh [ty]
> pattern DWIT t       = DC Wit [t]
> -- [/Feature = Prop]
> -- [Feature = Equality]
> pattern DEXT f       = DC Ext [f]
> -- [/Feature = Equality]
> -- [Feature = Sigma] 
> pattern DSIGMA p q = DC Sigma [p , q]
> pattern DPAIR  p q = DC Pair [p , q]
> pattern DUNIT      = DC One []
> pattern DVOID      = DC Zero []
> pattern DTIMES x y = DC Sigma [x , DL (DK y)]
> -- [/Feature = Sigma]
> -- [Feature = Enum]
> pattern DENUMU      = DC EnumU [] 
> pattern DENUMT e    = DC EnumT [e] 
> pattern DNILE       = DC NilE [] -- DCON (DPAIR {-(DTAG "nil")-} DZE DVOID)
> pattern DCONSE t e  = DC ConsE [t, e] -- DCON (DPAIR {- (DTAG "cons") -} (DSU DZE) (DPAIR t (DPAIR e DVOID)))
> pattern DZE         = DC Ze []
> pattern DSU n       = DC Su [n]
> -- [/Feature = Enum]
> -- [Feature = UId]
> pattern DUID    = DC UId []
> pattern DTAG s  = DC (Tag s) []
> -- [/Feature = UId] 
> {-- import <- CanDisplayPats
> -- [Feature = Anchor]
> pattern DANCHOR s args = DAnchor s args
> -- [/Feature = Anchor]
> -- [Feature = IDesc]
> pattern DIVARN     = DZE
> pattern DICONSTN   = DSU DZE
> pattern DIPIN      = DSU (DSU DZE)
> pattern DIFPIN     = DSU (DSU (DSU DZE))
> pattern DISIGMAN   = DSU (DSU (DSU (DSU DZE)))
> pattern DIFSIGMAN  = DSU (DSU (DSU (DSU (DSU DZE))))
> pattern DIPRODN    = DSU (DSU (DSU (DSU (DSU (DSU DZE)))))

> pattern DIMU l ii x i  = DIMu (l :?=: (Id ii :& Id x)) i
> pattern DIVAR i        = DCON (DPAIR DIVARN     (DPAIR i DVOID))
> pattern DIPI s t       = DCON (DPAIR DIPIN      (DPAIR s (DPAIR t DVOID)))
> pattern DIFPI s t      = DCON (DPAIR DIFPIN     (DPAIR s (DPAIR t DVOID)))
> pattern DISIGMA s t    = DCON (DPAIR DISIGMAN   (DPAIR s (DPAIR t DVOID)))
> pattern DIFSIGMA s t   = DCON (DPAIR DIFSIGMAN  (DPAIR s (DPAIR t DVOID)))
> pattern DICONST p      = DCON (DPAIR DICONSTN   (DPAIR p DVOID))
> pattern DIPROD u x y   = DCON (DPAIR DIPRODN    (DPAIR u (DPAIR x (DPAIR y DVOID))))
> -- [/Feature = IDesc]
> -- [Feature = Labelled]
> pattern DLABEL l t = DC (Label l t)
> pattern DLRET t    = DC (LRet t)
> -- [/Feature = Labelled]
> -}

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


