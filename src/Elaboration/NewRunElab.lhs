\section{Implementing the |Elab| monad}
\label{sec:Elaborator.RunElab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.NewRunElab where

> import Prelude hiding (foldl, exp)

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Traversable
> import Data.Foldable

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.Structure
> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation
> import ProofState.Interface
> import ProofState.NameResolution

> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import Tactics.Matching

< import Tactics.PropositionSimplify
< import Tactics.Unification

> import Elaboration.NewElabMonad

> import Distillation.Distiller

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace
> import Kit.NatFinVec


%endif

\subsection{Running elaboration processes}
\label{subsec:Elaborator.RunElab.runElab}


> runElab :: Feeder -> NewElab EXP -> ProofState (EXP, ElabStatus)

> data ElabStatus = ElabSuccess | ElabSuspended deriving Eq

> runElab _ (EReturn x) = return (x, ElabSuccess)

> runElab (nf, es) (EFeed e c) = runElab (nf+1, e:es) (c nf)

> runElab fes@(nf, es) (ELatest f c) = 
>   runElab fes (c (ev $ es !! (nf - (f+1))))

> runElab fes@(nf,es) el@(ECan f c) =
>   case ev (es !! (nf - (f+1))) of
>     ca :- as -> do
>       let las = length as 
>       runElab (nf+las, as++es) (c (ca,reverse (take las [nf..]))) 
>     _ :$ _ -> do 
>       e <- suspendElab fes el 
>       (| (e, ElabSuspended) |)
>     _ -> undefined -- cry

> runElab fes@(nf, es) (EHope (s :<: sub) c) = do
>   makeModule s
>   goIn
>   ty <- runSubElab sub 
>   moduleToGoal ty
>   putHoleKind Hoping
>   d <- getCurrentDefinition
>   goOut
>   runElab (nf+1, (D d :$ B0):es) (c nf)

> runElab fes@(nf, es) (EElab (s :<: sub) c) = do
>   makeModule s
>   goIn
>   (t,as) <- runSubElab sub
>   moduleToGoal (Prob t :- as)
>   let las = length as
>   (e,_) <- runElab (las, as) (probElab t (reverse (take las [0..])))
>   d <- giveOutBelow e 
>   runElab (nf+1, (D d :$ B0):es) (c nf)

> runElab fes@(nf, es) (EDub t c) = do
>   ps <- getParamsInScope'
>   case dub (bwdList (map (\(_,_,ty) -> ev ty) ps)) of
>       Just (_S, s) -> runElab (nf+2,(_S : s : es)) (c (nf :<: nf+1))
>       Nothing -> error "runElab EDub" -- cry
>     where dub :: Bwd VAL -> Maybe (EXP, EXP)
>           dub B0 = Nothing
>           dub (_ :< DUB u _S s) | t == u = (| (_S, s) |)
>           dub (vz :< _) = dub vz

> runElab fes e@(EInst n ex c) = do
>     inScope <- getInScope
>     case find ((Just n ==) . entryName) inScope of
>       Just (EDef d dev _) -> case devTip dev of 
>         Defined _ -> 
>           if equal 0 (defTy d :>: (D d :$ B0, ex))
>             then runElab fes c
>             else error "runElab EInst 1" -- cry
>         Unknown _ _ -> (| (,ElabSuspended) (suspendElab fes e) |)
>         _ -> error "runElab EInst 2" -- cry
>       _ -> error "runElab EInst 3" -- cry
 

> runSubElab :: SubElab x -> ProofState x
> runSubElab (SELambda sty c) = do
>   h <- assumeParam sty
>   runSubElab (c $ h :$ B0)

> runSubElab (SEReturn x) = return x

> suspendElab :: Feeder -> NewElab EXP -> ProofState EXP
> suspendElab fes prob = do
>     tip <- getDevTip
>     case tip of 
>       Unknown tt hk -> do 
>         putDevTip (SusElab tt (fes, prob) hk)
>         getCurrentDefinitionLocal
>       _ -> error "Suspend elab" -- Hopefully we never get here? 

> eSplit :: Feed -> NewElab (Feed, Feed)
> eSplit f = do
>     e <- eLatest f
>     f0 <- eFeed (exp $ e $$ Hd)
>     f1 <- eFeed (exp $ e $$ Tl)
>     return (f0,f1)

> eFeeds :: [EXP] -> NewElab [Feed]
> eFeeds = traverse eFeed 

> eLatests :: [Feed] -> NewElab [VAL]
> eLatests = traverse eLatest
