\section{Operators}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Operators where

> import BwdFwd
> import Tm
> import Features
> import Prop

%endif

> import <- OpCode

> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

