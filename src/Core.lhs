\section{Core}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Core where

> import Data.Foldable
> import Control.Monad
> import Control.Applicative

> import BwdFwd
> import Tm
> import Root

%endif

> type Dev = (Bwd Entry, Tip)

> data Tip
>   = Module
>   | Unknown VAL
>   | Defined INTM VAL
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




