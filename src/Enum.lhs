\section{Enum}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Enum where

%endif

> import -> CanConstructors where
>   EnumU  :: Can t
>   EnumT  :: t -> Can t
>   NilE   :: Can t
>   ConsE  :: t -> t -> Can t
>   Ze     :: Can t
>   Su     :: t -> Can t 

> import -> CanPats where
>   pattern UID      = C UId
>   pattern ENUMU    = C EnumU 
>   pattern ENUMT e  = C (EnumT e) 

> import -> TraverseCan where
>   traverse f EnumU        = (|EnumU|)
>   traverse f (EnumT e)    = (|EnumT (f e)|)
>   traverse f NilE         = (|NilE|)
>   traverse f (ConsE t e)  = (|ConsE (f t) (f e)|)
>   traverse f Ze           = (|Ze|)
>   traverse f (Su n)       = (|Su (f n)|) 

> import -> CanTyRules where
>   canTy ev (Set :>: EnumU)    = Just EnumU
>   canTy ev (Set :>: EnumT e)  =  Just (EnumT (ENUMU :>: e))
>   canTy ev (EnumU :>: NilE)       = Just NilE
>   canTy ev (EnumU :>: ConsE t e)  = Just (ConsE (UID :>: t) (ENUMU :>: e))
>   canTy ev (EnumT (C (ConsE t e)) :>: Ze)    = Just Ze 
>   canTy ev (EnumT (C (ConsE t e)) :>: Su n)  = Just (Su (ENUMT e :>: n)) 
