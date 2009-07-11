\section{Core}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Core where

> import Data.Foldable
> import Control.Monad
> import Control.Monad.State
> import Control.Applicative

> import BwdFwd
> import Tm

%endif

> type Dev = (Bwd Entry, Tip)

> data Tip
>   = Module
>   | Unknown VAL
>   | Defined INTM VAL
>   deriving Show

> data Entry
>   = REF :-: Entity
>   deriving Show

> data Entity
>   = Boy   BoyKind
>   | Girl  GirlKind Dev
>   deriving Show
>
> data BoyKind   = LAM | PI deriving (Show, Eq)
> data GirlKind  = LET deriving (Show, Eq)

> data Layer = Layer
>   {  elders  :: Bwd Entry
>   ,  mother  :: REF
>   ,  cadets  :: Fwd Entry
>   ,  laytip  :: Tip }
>   deriving Show

> type WhereAmI = (Bwd Layer, Dev)

> boys :: WhereAmI -> [REF]
> boys (ls, (es, _)) = foldMap (foldMap boy . elders) ls ++ foldMap boy es where
>   boy (r :-: Boy _)  = [r]
>   boy _              = []

> type Construct = State WhereAmI

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




