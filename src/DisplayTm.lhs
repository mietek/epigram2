\section{DisplayTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
>     ScopedTypeVariables,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

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
>     DL     :: DScope x                   -> InDTm  x -- \(\lambda\)
>     DC     :: Can (InDTm x)              -> InDTm  x -- canonical
>     DN     :: ExDTm x                    -> InDTm  x -- neutral
>     DQ     :: String                     -> InDTm  x -- hole
>     DI     :: String                     -> InDTm  x -- underscore
>     DT     :: InTmWrap x                 -> InDTm  x -- embedding
>     Dum    ::                               InDTm  x -- dummy
>     import <- InDTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)



> data ExDTm :: * -> * where
>     DP     :: x                          -> ExDTm  x -- parameter
>     DV     :: Int                        -> ExDTm  x -- variable
>     (::@)  :: Op -> [InDTm x]            -> ExDTm  x -- fully applied op
>     (::$)  :: ExDTm x -> Elim (InDTm x)  -> ExDTm  x -- elim
>     (::?)  :: InDTm x -> InDTm x         -> ExDTm  x -- typing
>     import <- ExDTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)

> data DScope :: * -> * where
>     (::.)  :: String -> InDTm x          -> DScope x  -- binding
>     DK     :: InDTm x                    -> DScope x  -- constant
>   deriving (Functor, Foldable, Traversable, Show)

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
> m %$ DI s          = pure (DI s)
> m %$ Dum           = (|Dum|)
> import <- DMangleRules
> _ %$ tm            = error ("%$: can't dmangle " ++ show (fmap (\_ -> ".") tm)) 

> dexMang ::  Applicative f => DMangle f x y ->
>            ExDTm x -> f (DSpine y) -> f (ExDTm y)
> dexMang m (DP x)     es = dmangP m x es
> dexMang m (DV i)     es = dmangV m i es
> dexMang m (o ::@ a)  es = (|(| (o ::@) ((m %$) ^$ a) |) $::$ es|) 
> dexMang m (t ::$ e)  es = dexMang m t (|((m %$) ^$ e) : es|)
> dexMang m (t ::? y)  es = (|(|(m %$ t) ::? (m %$ y)|) $::$ es|)
> import <- DExMangleRules
> dexMang _ tm         es = error ("dexMang: can't cope with " ++ show (fmap (\_ -> ".") tm))


> (%%$) :: DMangle Identity x y -> InDTm x -> InDTm y
> m %%$ t = runIdentity $ m %$ t

> type DSpine x = [Elim (InDTm x)]
>
> ($::$) :: ExDTm x -> DSpine x -> ExDTm x
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



> data InTmWrap x = InTmWrap (InTm x)

> instance Functor InTmWrap where
>   fmap = fmapDefault
> instance Foldable InTmWrap where
>   foldMap = foldMapDefault
> instance Traversable InTmWrap where
>   traverse f (InTmWrap x) = (| InTmWrap (traverse f x) |)
> instance Show x => Show (InTmWrap x) where
>   show (InTmWrap t) = show t
