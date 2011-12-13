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
> import Data.List

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

> data ElabResult  =  ElabSuccess EXP 
>                  |  ElabWaitCan Feeder Feed ((Can, [Feed]) -> NewElab EXP)
>                  |  ElabGoInst Feeder DEF (TY :>: EXP) (NewElab EXP) 
>                  |  ElabFailed StackError

> runElab :: Feeder -> NewElab EXP -> ProofState ElabResult

> runElab _ (EReturn x) = return (ElabSuccess x)

> runElab (nf, es) (EFeed e c) = runElab (nf+1, e:es) (c nf)

> runElab fes@(nf, es) (ELatest f c) = 
>   runElab fes (c (ev $ es !! (nf - (f+1))))

> runElab fes@(nf,es) el@(ECan f c) =
>   case ev (es !! (nf - (f+1))) of
>     ca :- as -> do
>       let las = length as 
>       runElab (nf+las, as++es) (c (ca,reverse (take las [nf..]))) 
>     _ :$ _ -> do 
>       (| (ElabWaitCan fes f c) |)
>     _ -> error "ECan" -- cry

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
>   nom <- makeModule s
>   goIn
>   (t,as) <- runSubElab sub
>   moduleToGoal (Prob t :- as)
>   let las = length as
>   er <- runElab (las, as) (probElab t (reverse (take las [0..])))
>   case er of
>     ElabSuccess e -> do 
>       d <- giveOutBelow e
>       runElab (nf+1, (D d :$ B0):es) (c nf)
>     ElabWaitCan fes dc cc -> do
>       d <- suspendElab fes (ECan dc cc)
>       goOut
>       runElab (nf+1, (D d :$ B0):es) (c nf)
>     ElabGoInst fes d te ci -> do
>       d <- getCurrentDefinition
>       goOut 
>       suspendElab (nf+1, (D d :$ B0):es) (c nf)
>       goIn
>       (| (ElabGoInst fes d te ci) |)
>     ElabFailed s -> (| (ElabFailed s) |)

> runElab fes@(nf, es) (EDub t c) = do
>   ps <- getParamsInScope'
>   case dub (bwdList (map (\(_,_,ty) -> ev ty) ps)) of
>       Just (_S, s) -> runElab (nf+2,(_S : s : es)) (c (nf :<: nf+1))
>       Nothing -> error "runElab EDub" -- cry
>     where dub :: Bwd VAL -> Maybe (EXP, EXP)
>           dub B0 = Nothing
>           dub (_ :< DUB u _S s) | t == u = (| (_S, s) |)
>           dub (vz :< _) = dub vz

> runElab fes e@(EInst d@(DEF _ _ op) (ty :>: ex) c) = do
>     inScope <- getInScope
>     lev <- getDevLev
>     case op of
>       -- suspend and wait for ambulando to solve
>       Hole -> (| (ElabGoInst fes d (ty :>: ex) c) |)
>       _ -> if equal lev (ty :>: (def d $$$ paramSpine inScope, ex))
>              then runElab fes c
>              else error "runElab EInst" -- cry
 
> runElab fes (ECry s) = (| (ElabFailed s) |)

> runSubElab :: SubElab x -> ProofState x
> runSubElab (SELambda sty c) = do
>   h <- assumeParam sty
>   runSubElab (c $ h :$ B0)

> runSubElab (SEReturn x) = return x


> suspendElab :: Feeder -> NewElab EXP -> ProofState DEF
> suspendElab fes prob = do
>     tip <- getDevTip
>     case tip of 
>       Unknown tt hk -> do 
>         putDevTip (SusElab tt (fes, prob) hk)
>         getCurrentDefinition
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
