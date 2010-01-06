\section{DisplayTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

> module DisplayTm where

> import Control.Applicative
> import Control.Monad.Identity

> import BwdFwd
> import Features
> import MissingLibrary
> import Tm

%endif

%format ::$ = ":\!\!:\!\!\$"
%format ::@ = ":\!\!:\!\!@"
%format ::? = ":\!:\!\in"
%format ::. = ":\!\bullet"

> data DTm :: {Dir} -> * -> * where
>   DL     :: DScope x                         -> DTm {In}  x -- \(\lambda\)
>   DC     :: Can (DTm {In} x)                 -> DTm {In}  x -- canonical
>   DN     :: DTm {Ex} x                       -> DTm {In}  x -- neutral
>   DQ     :: String                           -> DTm {In}  x -- hole

>   DP     :: x                                -> DTm {Ex}  x -- parameter
>   DV     :: Int                              -> DTm {Ex}  x -- variable
>   (::@)  :: Op -> [DTm {In} x]               -> DTm {Ex}  x -- fully applied op
>   (::$)  :: DTm {Ex} x -> Elim (DTm {In} x)  -> DTm {Ex}  x -- elim
>   (::?)  :: DTm {In} x -> DTm {In} x         -> DTm {Ex}  x -- typing

>   DT     :: Tm {d, TT} x                     -> DTm {d}   x -- embedding

> data DScope :: * -> * where
>   (::.)  :: String -> DTm {In} x           -> DScope x  -- binding
>   DK     :: DTm {In} x                     -> DScope x  -- constant

> type InDTm = DTm {In}
> type ExDTm = DTm {Ex}

> type INDTM  = InDTm REF 
> type EXDTM  = ExDTm REF

> pattern DSET       = DC Set               
> pattern DPI s t    = DC (Pi s t)          
> pattern DARR s t   = DPI s (DL (DK t))
> pattern DCON t     = DC (Con t)
> pattern DNV n      = DN (DV n)
> pattern DNP n      = DN (DP n)
> pattern DLAV x t   = DL (x ::. t)
> pattern DPIV x s t = DPI s (DLAV x t)

> import <- DisplayCanPats


> unelaborate :: Tm {d, TT} x -> DTm {d} x
> unelaborate (L s)       = DL (scopeToDScope s)
> unelaborate (C c)       = DC (fmap unelaborate c)
> unelaborate (N n)       = DN (unelaborate n)
> unelaborate (P s)       = DP s
> unelaborate (V i)       = DV i
> unelaborate (n :$ e)    = unelaborate n ::$ fmap unelaborate e
> unelaborate (op :@ vs)  = op ::@ fmap unelaborate vs
> unelaborate (t :? y)    = unelaborate t ::? unelaborate y

> scopeToDScope :: Scope {TT} x -> DScope x
> scopeToDScope (x :. t) = x ::. (unelaborate t)
> scopeToDScope (K t)    = DK (unelaborate t)

> dfortran :: DTm {In} x -> String
> dfortran (DL (x ::. _)) | not (null x) = x
> dfortran _ = "x"


> data DMangle f x y = DMang
>   {  dmangP :: x -> f [Elim (InDTm y)] -> f (ExDTm y)
>   ,  dmangV :: Int -> f [Elim (InDTm y)] -> f (ExDTm y)
>   ,  dmangB :: String -> DMangle f x y
>   }


> (%$) :: Applicative f => DMangle f x y -> DTm {In} x -> f (DTm {In} y)
> m %$ DL (DK t)      = (|DL (|DK (m %$ t)|)|)
> m %$ DL (x ::. t)   = (|DL (|(x ::.) (dmangB m x %$ t)|)|)
> m %$ DC c          = (|DC ((m %$) ^$ c)|)
> m %$ DN n          = (|DN (dexMang m n (|[]|))|)

> dexMang ::  Applicative f => DMangle f x y ->
>            DTm {Ex} x -> f [Elim (DTm {In} y)] -> f (DTm {Ex} y)
> dexMang m (DP x)     es = dmangP m x es
> dexMang m (DV i)     es = dmangV m i es
> dexMang m (o ::@ a)  es = (|(| (o ::@) ((m %$) ^$ a) |) $::$ es|) 
> dexMang m (t ::$ e)  es = dexMang m t (|((m %$) ^$ e) : es|)
> dexMang m (t ::? y)  es = (|(|(m %$ t) ::? (m %$ y)|) $::$ es|)

> (%%$) :: DMangle Identity x y -> DTm {In} x -> DTm {In} y
> m %%$ t = runIdentity $ m %$ t

> type DSpine p x = [Elim (DTm {In} x)]
>
> ($::$) :: DTm {Ex} x -> DSpine p x -> DTm {Ex} x
> ($::$) = foldl (::$)


> dunder :: Int -> x -> DMangle Identity x x
> dunder i y = DMang
>   {  dmangP = \ x ies -> (|(DP x $::$) ies|)
>   ,  dmangV = \ j ies -> (|((if i == j then DP y else DV j) $::$) ies|)
>   ,  dmangB = \ _ -> dunder (i + 1) y
>   }

> underDScope :: DScope x -> x -> InDTm x
> underDScope (DK t)     _ = t
> underDScope (_ ::. t)  x = dunder 0 x %%$ t




> instance Show x => Show (DTm d x) where
>   show (DL s)       = "DL (" ++ show s ++ ")"
>   show (DC c)       = "DC (" ++ show c ++ ")"
>   show (DN n)       = "DN (" ++ show n ++ ")"
>   show (DQ s)       = "?" ++ s
>   show (DP x)       = "DP (" ++ show x ++ ")"
>   show (DV i)       = "DV " ++ show i
>   show (n ::$ e)    = "(" ++ show n ++ " ::$ " ++ show e ++ ")"
>   show (op ::@ vs)  = "(" ++ opName op ++ " ::@ " ++ show vs ++ ")"
>   show (t ::? y)    = "(" ++ show t ++ " ::? " ++ show y ++ ")"
>   show (DT t)       = "DT (" ++ show t ++ ")"
>
> instance Show x => Show (DScope x) where
>   show (x ::. t)   = show x ++ " :. " ++ show t
>   show (DK t) = "DK (" ++ show t ++")"

