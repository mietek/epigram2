\section{Update}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Update where
> 
> import Data.Foldable
> import Control.Monad
> import Control.Applicative
> import Data.Traversable
> import Data.Monoid
> import Control.Monad.Writer

> import BwdFwd
> import Tm
> import Root
> import Developments

%endif

> afind :: Eq x => [x] -> x -> Writer Any x
> afind []     y = return y
> afind (x:xs) y = if x == y then tell (Any True) >> return x else afind xs y

> update :: (Traversable f,Eq x) => [x] -> f x -> Writer Any (f x)
> update xs  = traverse (afind xs)

> updateDev :: [REF] -> Dev -> Writer Any Dev
> updateDev rs d = traverseDev (afind rs) d
