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

> import SourceLang.SourceData 

%endif

> type Feed = Int -- DeBruijn level into an Env (list of stuffs) -- 0 is the last thing in the env

> type Feeder = (Int, [EXP])

The instruction signature given above is implemented using the following monad.

> data NewElab :: * -> * where
>     EReturn  :: x -> NewElab x
>     EFeed    :: EXP -> (Feed -> NewElab x) -> NewElab x
>     -- Stash an expression away so that it gets updated by News, get back a feed for that exp
>     ELatest  :: Feed -> (VAL -> NewElab x) -> NewElab x
>     -- Look up the latest copy of a Feed, get back the value of that Feed
>     ECan     :: Feed -> ((Can, [Feed]) -> NewElab x) -> NewElab x
>     -- Wait for the value of a feed to become canonical, get back the Can, and Feeds for its args
>     EHope    :: String :<: SubElab TY -> (Feed -> NewElab x) -> NewElab x
>     -- Hope for a value of the given type to turn up, get back a Feed for that value
>     EElab    :: Problem t => String :<: SubElab (t, [EXP]) -> (Feed -> NewElab x) -> NewElab x
>     -- Kick off a sub-elaboration problem, get back a Feed for its result
>     EDub     :: Template -> ((Feed {- Thing -} :<: Feed {- Scheme -}) -> NewElab x) -> NewElab x
>     -- Look up the evidence language term assoc. to some source language template, get back feeds for its value and Scheme
>     EInst    :: (Name, Feed) -> (TY :>: Feed) -> NewElab x -> NewElab x
>     -- Ask for some DEF to be unified with an expression
>     ECry     :: StackError -> NewElab x
>     -- Fail with some error

> instance Show x => Show (NewElab x) where
>   show (EInst d x c) = "EInst: " ++ show d ++ " " ++ show x
>   show (ECan x c) = "ECan"
>   show (ECry s) = "ECry: " ++ show s
>   show _ = "NewElab!!!"

> data SubElab :: * -> * where
>     SEReturn  :: x -> SubElab x
>     SELambda  :: (String :<: TY) -> (VAL -> SubElab x) -> SubElab x  

> instance Show x => Show (SubElab x) where
>   show _ = "SubElab!!!"

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
>   ECry x >>= _ = ECry x

To use the do notation, we define these operator versions of the Elab combinators

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

> eInst :: (Name, Feed) -> (TY :>: Feed) -> NewElab ()
> eInst n e = EInst n e (EReturn ())

> eCry :: StackError -> NewElab a
> eCry = ECry

> instance Monad SubElab where
>   return = SEReturn
>   SEReturn x >>= k = k x
>   SELambda sty c >>= k = SELambda sty ((k =<<) . c)

> seLambda :: (String :<: TY) -> SubElab VAL
> seLambda sty = SELambda sty SEReturn
