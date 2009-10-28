> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Desc where

> import -> CanConstructors where
>   Desc   :: Can t
>   Mu     :: t -> Can t
>   Done   :: Can t
>   Arg    :: t -> t -> Can t
>   Ind    :: t -> t -> Can t
>   Intros :: t -> Can t

> import -> TraverseCan where
>   traverse _ Desc       = (|Desc|)
>   traverse f (Mu x)     = (|Mu (f x)|)
>   traverse _ Done       = (|Done|)
>   traverse f (Arg x y)  = (|Arg (f x) (f y)|)
>   traverse f (Ind x y)  = (|Ind (f x) (f y)|)
>   traverse f (Intros x) = (|Intros (f x)|)

> import -> CanPats where
>   pattern DESC     = C Desc
>   pattern MU x     = C (Mu x)
>   pattern DONE     = C Done
>   pattern ARG x y  = C (Arg x y)
>   pattern IND x y  = C (Ind x y)
>   pattern INTROS x = C (Intros x)

> import -> CanTyRules where
>   canTy tc (Set :>: Desc)     = Just Desc
>   canTy tc (Set :>: Mu x)     = DESC `tc` x &\ \ x _ -> Just (Mu x)
>   canTy tc (Desc :>: Done)    = Just Done
>   canTy tc (Desc :>: Arg x y) = 
>     SET `tc` x &\ \ x xv -> 
>     Arr xv DESC `tc` y &\ \ y _ -> Just (Arg x y)
>   canTy tc (Desc :>: Ind x y) =
>     SET `tc` x &\ \ x _ ->
>     DESC `tc` y &\ \ y _ -> Just (Ind x y)
>   canTy tc (Mu x :>: Intros y) =
>     descOp @@ [x, MU x] `tc` y &\ \ t _ -> Just (Intros t)

> import -> OpCode where
>   descOp :: Op
>   descOp = Op
>     { opName = "desc"
>     , opArity = 1
>     , opTy = dOpTy
>     , opRun = dOpRun
>     } where
>       dOpTy ev [x,y] = Just ([DESC :>: x,SET :>: y],SET)
>       dOpRun :: [VAL] -> Either NEU VAL
>       dOpRun [DONE,y]    = Right UNIT
>       dOpRun [ARG x y,z] = 
>         Right (SIGMA x 
>                      (L (H (B0 :< y :< z) 
>                            "" 
>                            (N (descOp :@ [N (V 2 :$ A (NV 0)),NV 1])))))
>       dOpRun [IND x y,z] = Right (PAIR (Arr x z) (descOp @@ [y,z]))
>       dOpRun [N x,_]     = Left x