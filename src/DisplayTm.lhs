\section{DisplayTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

> module DisplayTm where

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
>
> instance Show x => Show (DScope x) where
>   show (x ::. t)   = show x ++ " :. " ++ show t
>   show (DK t) = "DK (" ++ show t ++")"
