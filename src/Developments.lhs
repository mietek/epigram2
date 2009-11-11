\section{Developments}
\label{sec:developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Developments where

> import Data.Foldable
> import Control.Monad
> import Control.Applicative
> import Data.Traversable
> import BwdFwd
> import Tm
> import Root

%endif

The top level state of the system is represented by a |Module| (that is, a
|Dev| with a |Module| tip). Each |Dev| contains a list of entries, some
of which may have their own developments, creating a nested tree-like structure.
The list of entries is from top-to-bottom (so the topmost is the furthest left).
A |Dev| also keeps track of its |Root| for namespace handling purposes.

> type Dev = (Bwd Entry, Tip, Root)


A |Module| is the |Tip| of a top-level development. Developments contained
within a female |Entity| may represent |Unknown|s of a given type, or may be |Defined|
as a term with a given type.

> data Tip
>   = Module
>   | Unknown TY
>   | Defined INTM TY
>   deriving Show


An |Entry| consists of a |REF| with the last component of its |Name| and an |Entity|.

> data Entry
>   = E REF (String, Int) Entity
>   deriving Show

We can compare them for equality by comparing their references (presumably?).

> instance Eq Entry where
>     (E r1 _ _) == (E r2 _ _)  =  r1 == r2

The last component of the name is cached because we will need it quite frequently for
display purposes. We can easily (but inefficiently) extract it from a reference:

> lastName :: REF -> (String, Int)
> lastName (n := _) = last n


An |Entity| may be a |Boy| (which does not have children) or a |Girl| (which may do).
A |Girl| is a definition, with a (possibly empty) development of sub-objects, which
has a |Tip| that is |Unknown| or |Defined|.
A |Boy| represents a parameter (either a $\lambda$ or $\Pi$ abstraction), which scopes
over all following entries and the definition (if any) in its development.

> data Entity
>   = Boy   BoyKind
>   | Girl  GirlKind Dev
>   deriving Show
>
> data BoyKind   = LAMB | PIB INTM deriving (Show, Eq)
> data GirlKind  = LETG deriving (Show, Eq)


A |Dev| is not truly |Traversable|, but it supports |traverse|-like operations that update
its references:

> traverseDev :: Applicative f => (REF -> f REF) -> Dev -> f Dev
> traverseDev f (es, t, r) = 
>   (|(\x y z -> (x,y,z)) (traverse (traverseEntry f) es) (traverseTip f t) ~r|)

> traverseTip :: Applicative f => (REF -> f REF) -> Tip -> f Tip
> traverseTip f Module        = pure Module
> traverseTip f (Unknown v)   = (|Unknown (traverseVal f v)|)
> traverseTip f (Defined t v) = (|Defined (traverse f t) (traverseVal f v)|)

> traverseEntry :: Applicative f => (REF -> f REF) -> Entry -> f Entry
> traverseEntry f (E r (x,i) e) = (|E (f r) (pure (x,i)) (traverseEntity f e)|)

> traverseEntity :: Applicative f => (REF -> f REF) -> Entity -> f Entity
> traverseEntity f (Boy bk)     = (|Boy (traverseBK f bk)|)
> traverseEntity f (Girl gk dv) = (|Girl (traverseGK f gk) (traverseDev f dv)|)

> traverseBK :: Applicative f => (REF -> f REF) -> BoyKind -> f BoyKind
> traverseBK f LAMB = pure LAMB
> traverseBK f (PIB t) = (|PIB (traverse f t)|)

> traverseGK :: Applicative f => (REF -> f REF) -> GirlKind -> f GirlKind
> traverseGK f LETG = pure LETG
