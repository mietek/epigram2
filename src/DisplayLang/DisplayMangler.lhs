\section{Variable Manipulation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module DisplayLang.DisplayMangler where

> import Control.Applicative
> import Control.Monad.Identity

> import Kit.BwdFwd

> import Features.Features

> import Evidences.Tm

> import DisplayLang.DisplayTm

%endif

> data DMangle f x y = DMang
>   {  dmangP :: x -> f (DSpine y) -> f (ExDTm y)
>   ,  dmangV :: Int -> f (DSpine y) -> f (ExDTm y)
>   ,  dmangB :: String -> DMangle f x y
>   }


> (%$) :: Applicative f => DMangle f x y -> InDTm x -> f (InDTm y)
> m %$ DL (DK t)      = (|DL (|DK (m %$ t)|)|)
> m %$ DL (x ::. t)   = (|DL (|(x ::.) (dmangB m x %$ t)|)|)
> m %$ DC c          = (|DC ((m %$) ^$ c)|)
> m %$ DN n          = (|DN (dexMang m n (|[]|))|)
> m %$ DQ s          = pure (DQ s)
> m %$ DU            = (|DU|)
> import <- DMangleRules
> _ %$ tm            = error ("%$: can't dmangle " ++ show (fmap (\_ -> ".") tm)) 

> dexMang ::  Applicative f => DMangle f x y ->
>            ExDTm x -> f (DSpine y) -> f (ExDTm y)
> dexMang m (DP x)     es = dmangP m x es
> dexMang m (DV i)     es = dmangV m i es
> dexMang m (t ::$ e)  es = dexMang m t (|((m %$) ^$ e) : es|)
> dexMang m (DType ty) es = (| (| DType (m %$ ty) |) $::$ es |)
> import <- DExMangleRules
> dexMang _ tm         es = error ("dexMang: can't cope with " ++ show (fmap (\_ -> ".") tm))


> (%%$) :: DMangle Identity x y -> InDTm x -> InDTm y
> m %%$ t = runIdentity $ m %$ t





> dunder :: Int -> REF -> DMangle Identity x x
> dunder i y = DMang
>   {  dmangP = \ x ies -> (|(DP x $::$) ies|)
>   ,  dmangV = \ j ies -> (|((if i == j then DTEx (ExTmWrap (P y)) else DV j) $::$) ies|)
>   ,  dmangB = \ _ -> dunder (i + 1) y
>   }

> underDScope :: DScope x -> REF -> InDTm x
> underDScope (DK t)     _ = t
> underDScope (_ ::. t)  x = dunder 0 x %%$ t





