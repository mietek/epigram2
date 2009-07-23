\section{Core}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Core where

> import Data.Foldable
> import Control.Monad
> import Control.Applicative
> import Data.Traversable
> import BwdFwd
> import Tm
> import Root

%endif

> type Dev = (Bwd Entry, Tip)

> data Tip
>   = Module
>   | Unknown TY
>   | Defined INTM TY
>   deriving Show

> data Entry
>   = E REF (String, Int) Entity
>   deriving Show

> data Entity
>   = Boy   BoyKind
>   | Girl  GirlKind Dev
>   deriving Show
>
> data BoyKind   = LAMB | PIB INTM deriving (Show, Eq)
> data GirlKind  = LETG deriving (Show, Eq)

> data Layer = Layer
>   {  elders  :: Bwd Entry
>   ,  mother  :: REF
>   ,  cadets  :: Fwd Entry
>   ,  laytip  :: Tip }
>   deriving Show

> type WhereAmI = (Bwd Layer, Root, Dev)

> data Elab x
>   = Bale x
>   | Cry
>   | Hope
>   | EDef String INTM (Elab INTM) (VAL -> Elab x)
>   | ELam String (VAL -> Elab x)
>   | EPi String INTM (VAL -> Elab x)

> instance Monad Elab where
>   return = Bale
>   Bale x        >>= k = k x
>   Cry           >>= k = Cry
>   Hope          >>= k = Hope
>   EDef x y d f  >>= k = EDef x y d ((k =<<) . f)
>   ELam x f      >>= k = ELam x ((k =<<) . f)
>   EPi x y f     >>= k = EPi x y ((k =<<) . f)
>
> instance Functor Elab where
>   fmap = ap . return
>
> instance Applicative Elab where
>   pure = return
>   (<*>) = ap

> traverseDev :: Applicative f => (REF -> f REF) -> Dev -> f Dev
> traverseDev f (es, t) = 
>   (|(,) (traverse (traverseEntry f) es) (traverseTip f t)|)

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
