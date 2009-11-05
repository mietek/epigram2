\section{Rooty}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Rooty where

> import Control.Applicative

> import BwdFwd
> import Root
> import Tm

%endif

Basically, a Reader monad on steroid

> class (Applicative m, Monad m) => Rooty m where
>     freshRef :: (String :<: TY) -> (REF -> m t) -> m t
>     forkRoot :: String -> m s -> (s -> m t) -> m t
>     root :: m Root

> instance Rooty ((->) Root) where
>     freshRef = Root.freshRef
>     forkRoot s child dad root = (dad . child) (room root s) (roos root)
>     root r = r