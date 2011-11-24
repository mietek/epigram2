\section{The |NewElab| monad: a DSL for elaboration}
\label{sec:NewElaboration.ElabMonad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards, RankNTypes, KindSignatures #-}

> module Elaboration.NewElabMonad where

> import Kit.NatFinVec

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.ErrorHandling

> import DisplayLang.Name
> import DisplayLang.Scheme


%endif

> type Feed = Int -- DeBruijn level into an Env (list of stuffs) -- 0 is the last thing in the env

> type Feeder = (Int, [EXP])

> type Template = String

The instruction signature given above is implemented using the following monad.

> data NewElab :: * -> * where
>     EReturn  :: x -> NewElab x
>     EFeed    :: EXP -> (Feed -> NewElab x) -> NewElab x
>     ELatest  :: Feed -> (VAL -> NewElab x) -> NewElab x
>     ECan     :: Feed -> ((Can, [Feed]) -> NewElab x) -> NewElab x
>     EHope    :: String :<: SubElab TY -> (Feed -> NewElab x) -> NewElab x
>     EElab    :: Problem t => String :<: SubElab (t, [EXP]) -> (Feed -> NewElab x) -> NewElab x
>     EDub     :: Template -> ((Feed {- Thing -} :<: Feed {- Scheme -}) -> NewElab x) -> NewElab x
>     EInst    :: Name -> EXP -> NewElab x -> NewElab x

> instance Show x => Show (NewElab x) where
>   show = undefined

> data SubElab :: * -> * where
>     SEReturn  :: x -> SubElab x
>     SELambda  :: (String :<: TY) -> (VAL -> SubElab x) -> SubElab x  

> instance Show x => Show (SubElab x) where
>   show = undefined

> instance Monad NewElab where
>   return = EReturn
>   EReturn x >>= k = k x
>   EFeed e c >>= k = EFeed e ((k =<<) . c)
>   ELatest f c >>= k = ELatest f ((k =<<) . c)
>   ECan f c >>= k = ECan f ((k =<<) . c)
>   EHope uty c >>= k = EHope uty ((k =<<) . c)
>   EElab e c >>= k = EElab e ((k =<<) . c)
>   EDub t c >>= k = EDub t ((k =<<) . c)
>   EInst n e c >>= k = EInst n e (k =<< c)

> eFeed :: EXP -> NewElab Feed
> eFeed e = EFeed e EReturn

> eLatest :: Feed -> NewElab VAL
> eLatest f = ELatest f EReturn

> eCan :: Feed -> NewElab (Can, [Feed])
> eCan f = ECan f EReturn

> eHope :: (String :<: SubElab TY) -> NewElab Feed
> eHope sty = EHope sty EReturn

> eElab :: Problem t => (String :<: SubElab (t, [EXP])) -> NewElab Feed
> eElab sp = EElab sp EReturn

> eDub :: Template -> NewElab (Feed {- Thing -} :<: Feed {- Scheme -}) 
> eDub t = EDub t EReturn

> eInst :: Name -> EXP -> NewElab ()
> eInst n e = EInst n e (EReturn ())

> instance Monad SubElab where
>   return = SEReturn
>   SEReturn x >>= k = k x
>   SELambda sty c >>= k = SELambda sty ((k =<<) . c)

> seLambda :: (String :<: TY) -> SubElab VAL
> seLambda sty = SELambda sty SEReturn

