\section{DisplayTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
>     ScopedTypeVariables,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module DisplayLang.DisplayTm where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable hiding (foldl)
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Features.Features

> import Evidences.Tm

%endif

%format ::$ = ":\!\!:\!\!\$"
%format ::. = ":\!\bullet"

> data InDTm :: * -> * where
>     DL     :: DScope x                   -> InDTm  x -- \(\lambda\)
>     DC     :: Can (InDTm x)              -> InDTm  x -- canonical
>     DN     :: ExDTm x                    -> InDTm  x -- neutral
>     DQ     :: String                     -> InDTm  x -- hole
>     DU     ::                               InDTm  x -- underscore
>     DT     :: InTmWrap x                 -> InDTm  x -- embedding
>     Dum    ::                               InDTm  x -- dummy
>     import <- InDTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)



> data ExDTm :: * -> * where
>     DP     :: x                          -> ExDTm  x -- parameter
>     DV     :: Int                        -> ExDTm  x -- variable
>     (::$)  :: ExDTm x -> Elim (InDTm x)  -> ExDTm  x -- elim
>     DType  :: InDTm x                    -> ExDTm  x -- type cast
>     DTEx   :: ExTmWrap x                 -> ExDTm  x -- embedding
>     import <- ExDTmConstructors
>  deriving (Functor, Foldable, Traversable, Show)


> data DScope :: * -> * where
>     (::.)  :: String -> InDTm x          -> DScope x  -- binding
>     DK     :: InDTm x                    -> DScope x  -- constant
>   deriving (Functor, Foldable, Traversable, Show)

> dScopeName :: DScope x -> String
> dScopeName (x ::. _)  = x
> dScopeName (DK _)      = "_"

> dScopeTm :: DScope x -> InDTm x
> dScopeTm (_ ::. tm)  = tm
> dScopeTm (DK tm)      = tm


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
> pattern DTY ty tm  = (DType ty) ::$ A tm

> import <- CanDisplayPats



We keeps track of the |Size| of terms when parsing and pretty-printing, to
avoid nasty left recursion and minimise the number of brackets we output.
When going left, the size decreases. Brackets may be used to wrap an
 expression of higher size.

> data Size = ArgSize | AppSize | EqSize | AndSize | ArrSize | PiSize | AscSize
>   deriving (Show, Eq, Enum, Bounded, Ord)


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
> m %$ DU            = (|DU|)
> m %$ Dum           = (|Dum|)
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

> type DSpine x = [Elim (InDTm x)]
>
> ($::$) :: ExDTm x -> DSpine x -> ExDTm x
> ($::$) = foldl (::$)



> dunder :: Int -> REF -> DMangle Identity x x
> dunder i y = DMang
>   {  dmangP = \ x ies -> (|(DP x $::$) ies|)
>   ,  dmangV = \ j ies -> (|((if i == j then DTEx (ExTmWrap (P y)) else DV j) $::$) ies|)
>   ,  dmangB = \ _ -> dunder (i + 1) y
>   }

> underDScope :: DScope x -> REF -> InDTm x
> underDScope (DK t)     _ = t
> underDScope (_ ::. t)  x = dunder 0 x %%$ t



> data InTmWrap x = InTmWrap INTM

> instance Functor InTmWrap where
>   fmap = fmapDefault
> instance Foldable InTmWrap where
>   foldMap = foldMapDefault
> instance Traversable InTmWrap where
>   traverse f (InTmWrap x) = pure (InTmWrap x)
> instance Show x => Show (InTmWrap x) where
>   show (InTmWrap t) = show t


> data ExTmWrap x = ExTmWrap EXTM

> instance Functor ExTmWrap where
>   fmap = fmapDefault
> instance Foldable ExTmWrap where
>   foldMap = foldMapDefault
> instance Traversable ExTmWrap where
>   traverse f (ExTmWrap x) = pure (ExTmWrap x)
> instance Show x => Show (ExTmWrap x) where
>   show (ExTmWrap t) = show t
