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
>   | Unknown (INTM :=>: TY)
>   | Defined INTM (INTM :=>: TY)
>   deriving Show


An |Entry| is either an |Entity| with its |REF| and the last component of its |Name|,
or a "news bulletin" |R| describing updates to future references.

> data Entry
>   =  E REF (String, Int) Entity
>   |  R NewsBulletin
>   deriving Show

We can compare them for equality by comparing their references (presumably?).

> instance Eq Entry where
>     (E r1 _ _) == (E r2 _ _)  =  r1 == r2
>     _ == _ = error "instance Eq Entry: cannot compare news bulletins for equality"

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


|News| represents possible changes to references. At the moment, it may be |GoodNews|
(the reference has become more defined) or |NoNews| (even better from our perspective,
as the reference has not changed). When we come to implement functionality to remove
definitions from the proof state, we will also need |BadNews| (the reference has
changed but is not more informative) and |DeletedNews| (the reference has gone completely).

> data News = GoodNews | NoNews deriving (Eq, Ord, Show)

> type NewsBulletin = [(REF, News)]

The |(-||)| operator takes a list of entries and a term, and changes the term
so that boys in the list of entries are represented by de Brujin indices.

> (-|) :: Bwd Entry -> INTM -> INTM
> es -| t = disMangle es 0 %% t
>   where
>     disMangle :: Bwd Entry -> Int -> Mangle I REF REF
>     disMangle ys i = Mang
>       {  mangP = \ x ies -> (|(h ys x i $:$) ies|)
>       ,  mangV = \ i ies -> (|(V i $:$) ies|)
>       ,  mangB = \ _ -> disMangle ys (i + 1)
>       }
>     h B0                        x i  = P x
>     h (ys :< E y _ (Boy _))     x i
>       | x == y     = V i
>       | otherwise  = h ys x (i + 1)
>     h (ys :< E y _ (Girl _ _))  x i = h ys x i

The |parBind| function $\lambda$-binds over a list $\Delta$ of entries and
$\lambda$- and $\Pi$-binds over a list $\nabla$.

> parBind ::  {- $\Delta$ :: -} Bwd Entry {- $\Gamma$ -} -> 
>             {- $\nabla$ :: -} Bwd Entry {- $\Gamma, \Delta$ -} -> 
>             INTM {- $\Gamma, \Delta, \nabla$ -} ->
>             INTM {- $\Gamma$ -}
> parBind delta nabla t = help delnab nabla (delnab -| t) where
>     delnab = delta <+> nabla
>     help B0                                      B0            t = t
>     help (delta   :< E _ _       (Girl _ _))     B0            t = help delta B0 t
>     help (delta   :< E _ (x, _)  (Boy _))        B0            t = help delta B0 (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Girl _ _))     (nabla :< _)  t = help delnab nabla t
>     help (delnab  :< E _ (x, _)  (Boy LAMB))     (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Boy (PIB s)))  (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))


A |Dev| is not truly |Traversable|, but it supports |traverse|-like operations that update
its references:

> traverseDev :: Applicative f => (REF -> f REF) -> Dev -> f Dev
> traverseDev f (es, t, r) = 
>   (|(\x y z -> (x,y,z)) (traverse (traverseEntry f) es) (traverseTip f t) ~r|)

> traverseTip :: Applicative f => (REF -> f REF) -> Tip -> f Tip
> traverseTip f Module                   = pure Module
> traverseTip f (Unknown (t :=>: v))     = (|Unknown (|traverse f t :=>: traverseVal f v|)|)
> traverseTip f (Defined tm (t :=>: v))  =
>   (|Defined (traverse f tm) (|traverse f t :=>: traverseVal f v|)|)

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
