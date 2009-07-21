\section{UId}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module UId where

%endif

> import -> CanConstructors where
>   UId    :: Can t
>   Tag    :: String -> Can t

> import -> TraverseCan where
>   traverse f UId          = (|EnumU|)
>   traverse f (Tag s)      = (|(Tag s)|)

> import -> CanTyRules where
>   canTy ev (Set :>: UId) = Just UId
>   canTy ev (UId :>: Tag s) = Just (Tag s)
