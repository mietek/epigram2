\section{Schemes}
\label{sec:DisplayLang.Scheme}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes #-}

> module DisplayLang.Scheme where

> import ShePrelude

> import Control.Applicative
> import Data.Foldable hiding (foldl)
> import Data.Traversable

> import Evidences.Tm

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Kit.NatFinVec

%endif

\subsection{Schemes for implicit arguments}



A definition may have a |Scheme|, which allows us to handle implicit
syntax. A |Scheme| is defined by:
%%
\[
\begin{array}{rll}
\SC{Scheme} ::= & \D{Ty}
                & \mbox{a real, tangible type} \\
             || & \PI{\V{x}}{\SC{Scheme}}{\SC{Scheme}}
                & \mbox{an explicit $\Pi$} \\
             || & \IPI{\V{x}}{\D{Ty}}{\SC{Scheme}}
                & \mbox{an implicit $\Pi$}
\end{array}
\]

Crucially, an implicit $\Pi$ hides a real type, not another scheme: we
forbid ``higher-schemes'' for mental sanity reasons. For the sake of
generality, we will parameterise over the exact representation of
types:


> data Sch :: * -> * where
>     SchType        :: x                           -> Sch x
>     SchExplicitPi  :: String :<: Sch x  -> Sch x  -> Sch x
>     SchImplicitPi  :: String :<: x      -> Sch x  -> Sch x
>   deriving Show

> type Scheme = Sch EXP
> type DScheme = Sch DInTmRN


%if False

> {-
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
> -}

%endif


\subsection{Extracting names}

Given a scheme, we can extract the names of its $\Pi$s:

> schemeNames :: Sch x -> [String]
> schemeNames (SchType _) = []
> schemeNames (SchExplicitPi (x :<: _) sch) = x : schemeNames sch
> schemeNames (SchImplicitPi (x :<: _) sch) = x : schemeNames sch


\subsection{Turning schemes to terms}

We can also convert a |Scheme| into a |Tm|:

> schemeToType :: pi (n :: Nat). [ EXP ] -> Scheme -> Tm {Body, Exp, n}
> schemeToType {n} es (SchType ty) = partCapture {n} es ty
> schemeToType {n} es (SchExplicitPi (x :<: s) t) = 
>     Pi :- [schemeToType {n} es s, L ENil x (schemeToType {S n} es t)]
> schemeToType {n} es (SchImplicitPi (x :<: s) t) =
>     Pi :- [partCapture {n} es s, L ENil x (schemeToType {S n} es t)]


\subsection{Unlifting schemes}

Schemes are stored fully $\Pi$-lifted with |SchExplicitPI|s, so we may
need to strip them of a spine of shared parameters:

> stripScheme :: Int -> Scheme -> Scheme
> stripScheme 0 sch = sch
> stripScheme n (SchExplicitPi (x :<: SchType s) schT) = stripScheme (n-1) schT


\subsection{Schemes in error messages}

We can cheaply embed schemes in error messages by converting them to types
and evaluating. Really, we ought to add schemes as a kind of |ErrorTok|.


< errScheme :: Scheme INTM -> ErrorItem t
< errScheme sch = errTyVal (evTm (schemeToInTm sch) :<: SET)

