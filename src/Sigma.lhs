> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Sigma where

> import -> CanConstructors where
>   Unit   :: Can t
>   Void   :: Can t
>   Sigma  :: t -> t -> Can t
>   Pair   :: t -> t -> Can t 

> import -> ElimConstructors where
>   Hd     :: Elim t
>   Tl     :: Elim t

> import -> ElimComputation where
>   C (Pair x y) $$ Hd = x
>   C (Pair x y) $$ Tl = y 
