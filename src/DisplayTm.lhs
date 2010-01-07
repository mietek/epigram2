\section{DisplayTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

> module DisplayTm where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable hiding (foldl)
> import Data.Traversable

> import BwdFwd
> import Features
> import MissingLibrary
> import Tm

%endif

%format ::$ = ":\!\!:\!\!\$"
%format ::@ = ":\!\!:\!\!@"
%format ::? = ":\!:\!\in"
%format ::. = ":\!\bullet"

> data InDTm :: * -> * where
>     DL     :: DScope x                         -> InDTm  x -- \(\lambda\)
>     DC     :: Can (InDTm x)                    -> InDTm  x -- canonical
>     DN     :: ExDTm x                          -> InDTm  x -- neutral
>     DQ     :: String                           -> InDTm  x -- hole
>     DI     :: String                           -> InDTm  x -- underscore
>     DT     :: InTm x                    -> InDTm  x -- embedding

> data ExDTm :: * -> * where
>     DP     :: x                                -> ExDTm  x -- parameter
>     DV     :: Int                              -> ExDTm  x -- variable
>     (::@)  :: Op -> [InDTm x]            -> ExDTm  x -- fully applied op
>     (::$)  :: ExDTm x -> Elim (InDTm x)  -> ExDTm  x -- elim
>     (::?)  :: InDTm x -> InDTm x         -> ExDTm  x -- typing

> data DScope :: * -> * where
>   (::.)  :: String -> InDTm x           -> DScope x  -- binding
>   DK     :: InDTm x                     -> DScope x  -- constant

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


> unelaborate :: InTm x -> InDTm x
> unelaborate (L s)       = DL (scopeToDScope s)
> unelaborate (C c)       = DC (fmap unelaborate c)
> unelaborate (N n)       = DN (unelaborateEx n)

> unelaborateEx :: ExTm x -> ExDTm x
> unelaborateEx (P s)       = DP s
> unelaborateEx (V i)       = DV i
> unelaborateEx (n :$ e)    = unelaborateEx n ::$ fmap unelaborate e
> unelaborateEx (op :@ vs)  = op ::@ fmap unelaborate vs
> unelaborateEx (t :? y)    = unelaborate t ::? unelaborate y

> scopeToDScope :: Scope {TT} x -> DScope x
> scopeToDScope (x :. t) = x ::. (unelaborate t)
> scopeToDScope (K t)    = DK (unelaborate t)

> dfortran :: InDTm x -> String
> dfortran (DL (x ::. _)) | not (null x) = x
> dfortran _ = "x"


> data DMangle f x y = DMang
>   {  dmangP :: x -> f [Elim (InDTm y)] -> f (ExDTm y)
>   ,  dmangV :: Int -> f [Elim (InDTm y)] -> f (ExDTm y)
>   ,  dmangB :: String -> DMangle f x y
>   }


> (%$) :: Applicative f => DMangle f x y -> InDTm x -> f (InDTm y)
> m %$ DL (DK t)      = (|DL (|DK (m %$ t)|)|)
> m %$ DL (x ::. t)   = (|DL (|(x ::.) (dmangB m x %$ t)|)|)
> m %$ DC c          = (|DC ((m %$) ^$ c)|)
> m %$ DN n          = (|DN (dexMang m n (|[]|))|)
> m %$ DQ s          = pure (DQ s)
> m %$ DI s          = pure (DI s)
> _ %$ tm            = error ("%$: can't dmangle " ++ show (fmap (\_ -> ".") tm)) 

> dexMang ::  Applicative f => DMangle f x y ->
>            ExDTm x -> f [Elim (InDTm y)] -> f (ExDTm y)
> dexMang m (DP x)     es = dmangP m x es
> dexMang m (DV i)     es = dmangV m i es
> dexMang m (o ::@ a)  es = (|(| (o ::@) ((m %$) ^$ a) |) $::$ es|) 
> dexMang m (t ::$ e)  es = dexMang m t (|((m %$) ^$ e) : es|)
> dexMang m (t ::? y)  es = (|(|(m %$ t) ::? (m %$ y)|) $::$ es|)

> (%%$) :: DMangle Identity x y -> InDTm x -> InDTm y
> m %%$ t = runIdentity $ m %$ t

> type DSpine p x = [Elim (InDTm x)]
>
> ($::$) :: ExDTm x -> DSpine p x -> ExDTm x
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




> instance Show x => Show (InDTm x) where
>   show (DL s)       = "DL (" ++ show s ++ ")"
>   show (DC c)       = "DC (" ++ show c ++ ")"
>   show (DN n)       = "DN (" ++ show n ++ ")"
>   show (DQ s)       = "?" ++ s
>   show (DI s)       = "_" ++ s
>   show (DT t)       = "DT (" ++ show t ++ ")"

> instance Show x => Show (ExDTm x) where
>   show (DP x)       = "DP (" ++ show x ++ ")"
>   show (DV i)       = "DV " ++ show i
>   show (n ::$ e)    = "(" ++ show n ++ " ::$ " ++ show e ++ ")"
>   show (op ::@ vs)  = "(" ++ opName op ++ " ::@ " ++ show vs ++ ")"
>   show (t ::? y)    = "(" ++ show t ++ " ::? " ++ show y ++ ")"
>
> instance Show x => Show (DScope x) where
>   show (x ::. t)   = show x ++ " :. " ++ show t
>   show (DK t) = "DK (" ++ show t ++")"



> instance Functor DScope where
>   fmap = fmapDefault
> instance Foldable DScope where
>   foldMap = foldMapDefault
> instance Traversable DScope where
>   traverse f (x ::. t)   = (|(x ::.) (traverse f t)|)
>   traverse f (DK t)      = (|DK (traverse f t)|)


> instance Functor InDTm where
>   fmap = fmapDefault
> instance Foldable InDTm where
>   foldMap = foldMapDefault
> instance Traversable InDTm where
>   traverse f (DL sc)     = (|DL (traverse f sc)|)
>   traverse f (DC c)      = (|DC (traverse (traverse f) c)|)
>   traverse f (DN n)      = (|DN (traverse f n)|)
>   traverse f (DQ s)      = pure (DQ s)
>   traverse f (DI s)      = pure (DI s)
>   traverse f (DT t)      = (|DT (traverse f t)|)

> instance Functor ExDTm where
>   fmap = fmapDefault
> instance Foldable ExDTm where
>   foldMap = foldMapDefault
> instance Traversable ExDTm where
>   traverse f (DP x)      = (|DP (f x)|)
>   traverse f (DV i)      = pure (DV i)
>   traverse f (t ::$ u)   = (|(::$) (traverse f t) (traverse (traverse f) u)|)
>   traverse f (op ::@ ts) = (|(op ::@) (traverse (traverse f) ts)|)
>   traverse f (tm ::? ty) = (|(::?) (traverse f tm) (traverse f ty)|)
