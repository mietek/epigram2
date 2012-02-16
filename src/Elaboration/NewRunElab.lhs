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
> import Tactics.PropositionSimplify
> import Tactics.ProblemSimplify

> import Elaboration.NewElabMonad

> import Distillation.Distiller

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace
> import Kit.NatFinVec

> import Debug.Trace

> import SourceLang.SourceData 

%endif

\subsection{Running elaboration processes}
\label{subsec:Elaborator.RunElab.runElab}

> data ElabResult  =  ElabSuccess EXP 
>                  |  ElabWaitCan Feeder Feed ((Can, [Feed]) -> NewElab EXP)
>                  |  ElabGoInst Int Name Feeder (Name, Feed) (TY :>: (EXP, Feed)) (NewElab EXP) 
>                  |  ElabFailed StackError
>                  |  ElabNothing

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
>   se <- heresHoping (ev ty) 
>   s <- runElab (0, []) se
>   case s of
>       ElabSuccess e -> do 
>         d <- give e
>         goOut'
>         as <- (| paramSpine getInScope |)
>         runElab (nf+1, (D d :$ as):es) (c nf)
>       ElabWaitCan fes dc cc -> do
>         d <- suspendElab fes (ECan dc cc)
>         goOut'
>         as <- (| paramSpine getInScope |)
>         runElab (nf+1, (D d :$ as):es) (c nf)
>       ElabGoInst i nam fes ime te ci -> do
>         goOut'
>         as <- (| paramSpine getInScope |)
>         suspendElab (nf+1, (D d :$ as):es) (c nf)
>         (| (ElabGoInst (i+1) nam fes ime te ci) |)
>       ElabFailed [] -> {- Currently stands for "Made no progress" -} do
>         goOut' 
>         as <- (| paramSpine getInScope |)
>         runElab (nf+1, (D d :$ as):es) (c nf)
>       ElabFailed s -> (| (ElabFailed s) |)
>     where heresHoping :: VAL -> ProofState (NewElab EXP)
>           heresHoping (PRF _P) = do
>             psimp <- runPropSimplify (ev _P)
>             case psimp of 
>               (SimplyTrivial prf) -> (| (| prf |) |)
>               (SimplyAbsurd _) -> (| (eCry [err "Proposition is absurd"]) |)
>               (Simply qs h) -> do
>                 lev <- getDevLev
>                 (| (do
>                   prfqfs <- eHopes (map (\(i,(x,_)) -> (("s" ++ show i) :<: (|x|))) (zip [0..] (trail qs)))
>                   prfqs <- eLatests prfqfs
>                   let prf = (zip [lev..] (map exp prfqs), INil) :/ h
>                   (| prf |) ) |)
>               CannotSimplify -> case (ev _P) of
>                 EQ _S s@(P (l,n,ty) :$ as) _T t@(P (l',n',ty') :$ as') 
>                   | l == l' , Just elfs <- zipSpine (as, as') -> (| (do
>                     fs <- elfs
>                     hopeSpine (ev ty :>: fs) (Refl ty (P (l ,n ,ty) :$ B0)) B0) |)

>                 SETEQ s@(P (l,n,ty) :$ as) t@(P (l',n',ty') :$ as') 
>                   | l == l' , Just elfs <- zipSpine (as, as') -> (| (do
>                     fs <- elfs
>                     x <- hopeSpine (ev ty :>: fs) (Refl ty (P (l ,n ,ty) :$ B0)) B0
>                     (| (x $$ Out) |) ) |) 

>                 {-
>                 EQ _S s@(D def :$ as) _T t@(D def' :$ bs) | Hole Hoping <- defOp def, Hole Hoping <- defOp def' ->
>                     case trace "POP" $ orderName (defName def) (defName def') of
>                          GREATER -> do
>                                nam <- getCurrentName
>                                (| (do
>                                    [_Sf, sf, _Tf, tf] <- eFeeds [_S, s, _T, t]
>                                    eInst (defName def, sf) (_T :>: tf)
>                                    [_T, t] <- eLatests [_Tf, tf]
>                                    (| (Refl (exp _T) (exp t) :$ B0) |) ) |)
>                          LESS -> do
>                                nam <- getCurrentName
>                                (| (do
>                                    [_Sf, sf, _Tf, tf] <- eFeeds [_S, s, _T, t]
>                                    eInst (defName def', tf) (_S :>: sf)
>                                    [_S, s] <- eLatests [_Sf, sf]
>                                    (| (Refl (exp _S) (exp s) :$ B0) |) ) |)
>                          EQUAL -> error "these two names are equal, so the propositional simplifier should have solved this already"

>                 EQ _S s@(D def :$ as) _T t | Hole Hoping <- defOp def -> do 
>                    nam <- getCurrentName
>                    (| (do
>                          [_Sf, sf, _Tf, tf] <- eFeeds [_S, s, _T, t]
>                          eInst (defName def, sf) (_T :>: tf)
>                          [_T, t] <- eLatests [_Tf, tf]
>                          (| (Refl (exp _T) (exp t) :$ B0) |) ) |)
>                 EQ _S s _T t@(D def :$ as) | Hole Hoping <- defOp def -> do 
>                    nam <- getCurrentName
>                    (| (do
>                          [_Sf, sf, _Tf, tf] <- eFeeds [_S, s, _T, t]
>                          eInst (defName def, tf) (_S :>: sf)
>                          [_S, s] <- eLatests [_Sf, sf]
>                          (| (Refl (exp _S) (exp s) :$ B0) |) ) |)

>                 SETEQ s@(D def :$ as) t@(D def' :$ bs) | Hole Hoping <- defOp def, Hole Hoping <- defOp def' ->
>                     case orderName (defName def) (defName def') of
>                       GREATER -> do
>                           nam <- getCurrentName
>                           (| (do
>                               [sf, tf] <- eFeeds [s, t]
>                               eInst (defName def, sf) (SET :>: tf)
>                               [t] <- eLatests [tf]
>                               (| (SetRefl (exp t) :$ B0) |) ) |)
>                       LESS -> do
>                           nam <- getCurrentName
>                           (| (do
>                               [tf, sf] <- eFeeds [t, s]
>                               eInst (defName def', tf) (SET :>: sf)
>                               [s] <- eLatests [sf]
>                               (| (SetRefl (exp s) :$ B0) |) ) |)
>                       EQUAL -> error "these two names are equal, so the propositional simplifier should have solved this already"

>                 SETEQ s@(D def :$ as) t | Hole Hoping <- defOp def -> do 
>                    nam <- getCurrentName
>                    (| (do
>                          [_Sf, tf] <- eFeeds [SET, t]
>                          eInst (defName def, _Sf) (SET :>: tf)
>                          [t] <- eLatests [tf]
>                          (| (SetRefl (exp t) :$ B0) |) ) |)
>                 SETEQ s t@(D def :$ as) | Hole Hoping <- defOp def -> do 
>                    nam <- getCurrentName
>                    (| (do
>                          [_Tf, sf] <- eFeeds [SET, s]
>                          eInst (defName def, _Tf) (SET :>: sf)
>                          [s] <- eLatests [sf]
>                          (| (SetRefl (exp s) :$ B0) |) ) |)
>                 -}
>                 _ -> (| (eCry []) |)
>           heresHoping ONE = (| (| ZERO |)|) 
>           heresHoping _ = (| (eCry []) |)

>           zipSpine :: (Bwd (Elim EXP), Bwd (Elim EXP)) -> Maybe (NewElab [(Feed, Feed)])
>           zipSpine (B0, B0) = (| (| [] |) |) 
>           zipSpine (ez :< A e, ez' :< A e') = do
>             r <- zipSpine (ez, ez')
>             (| (do 
>                   efsefs' <- r
>                   [ef, ef'] <- eFeeds [e, e']
>                   (| (efsefs' ++ [(ef,ef')]) |) ) |)
>           zipSpine x = Nothing

>           hopeSpine :: (VAL :>: [(Feed,Feed)]) -> Tm {Head, Exp, Z} -> Bwd (Elim Feed) -> NewElab EXP
>           hopeSpine (PI _A _B :>: ((af, af') : afsafs')) h fz = do
>             [a,a'] <- eLatests [af,af']
>             let _Pbit =  EQ _A (exp a) _A (exp a')
>             f <- trace ("bit: " ++ ugly V0 (ev _Pbit)) $ eHope ("bit" :<: (| (PRF _Pbit) |))
>             a <- eLatest af
>             hopeSpine (ev _B $$. a :>: afsafs') h (fz :< QA af af' f)
>           hopeSpine (_T :>: []) h fz = do
>             ez <- traverse (traverse (\ x -> (| exp (eLatest x) |))) fz
>             (| (h :$ ez) |)
>           hopeSpine _ _ _ = eCry []

> runElab fes@(nf, es) (EElab (s :<: sub) c) = do
>   nom <- makeModule s
>   goIn
>   (t,as) <- runSubElab sub
>   moduleToGoal (Prob t :- as)
>   d <- getCurrentDefinition
>   let las = length as
>   er <- runElab (las, as) (probElab t (reverse (take las [0..])))
>   case er of
>     ElabSuccess e -> do 
>       d <- give e
>       goOut'
>       as <- (| paramSpine getInScope |)
>       runElab (nf+1, (D d :$ as):es) (c nf)
>     ElabWaitCan fes dc cc -> do
>       d <- suspendElab fes (ECan dc cc)
>       goOut'
>       as <- (| paramSpine getInScope |)
>       runElab (nf+1, (D d :$ as):es) (c nf)
>     ElabGoInst i nam fes ime te ci -> do
>       d <- getCurrentDefinition
>       goOut'
>       as <- (| paramSpine getInScope |)
>       suspendElab (nf+1, (D d :$ as):es) (c nf)
>       (| (ElabGoInst (i+1) nam fes ime te ci) |)
>     ElabFailed s -> (| (ElabFailed s) |)

> runElab fes@(nf, es) (EDub t c) = do
>   ps <- getInScope
>   case dub ps of
>       Just (_S, s) -> runElab (nf+2,(_S : s : es)) (c (Just (nf :<: nf+1)))
>       Nothing -> runElab (nf,es) (c Nothing)
>     where dub :: Bwd (Entry Bwd) -> Maybe (EXP, EXP)
>           dub B0 = Nothing
>           dub (_ :< EParam _ _ ty _) | DUB u _S s <- ev ty , t == u = (| (_S, s) |)
>           dub (_ :< EDef _ (Dev{devTip = Defined (ty :>: _)}) _) | DUB u _S s <- ev ty , t == u = (| (_S, s) |)
>           dub (vz :< _) = dub vz

> runElab fes@(nf,es) e@(EInst (n, f) (ty :>: ex) c) = do
>     inScope <- getInScope
>     lev <- getDevLev
>     let x = es !! (nf - (f+1))
>         y = es !! (nf - (ex+1))
>     case ev x of
>       D d :$ _ | defName d == n -> do
>         suspendElab (nf, es) e
>         -- suspend and wait for ambulando to solve
>         nam <- getCurrentName
>         (| (ElabGoInst 0 nam fes (n,f) (ty :>: (y,ex)) c) |)
>       _ -> if equal lev (ty :>: (x, y))
>              then runElab fes c
>              else (| (ElabFailed [err $ "runElab EInst: " ++ show n ++ " -- " ++ show (ev x) ++ " =/= " ++ show (ev y)]) |) -- cry

 
> runElab fes (ECry s) = (| (ElabFailed s) |)

> runSubElab :: SubElab x -> ProofState x
> runSubElab (SELambda sty@(s :<: _) c) = do
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
>       SusElab tt _ hk -> do 
>         putDevTip (SusElab tt (fes, prob) hk)
>         getCurrentDefinition
>       _ -> error "Suspend elab" -- Hopefully we never get here? 


> eSplit :: Feed -> NewElab (Feed, Feed)
> eSplit f = do
>     e <- eLatest f
>     f0 <- eFeed (exp $ e $$ Hd)
>     f1 <- eFeed (exp $ e $$ Tl)
>     return (f0,f1)

> eFeeds :: Traversable f => f EXP -> NewElab (f Feed)
> eFeeds = traverse eFeed 

> eLatests :: Traversable f => f Feed -> NewElab (f VAL)
> eLatests = traverse eLatest

> eHopes :: Traversable f => f (String :<: SubElab TY) -> NewElab (f Feed)
> eHopes = traverse eHope

> ePi :: Feed -> NewElab (Feed, Feed)
> ePi _Tf = do
>   _T <- eLatest _Tf
>   case _T of
>     PI _A _B -> do
>       [_Af, _Bf] <- eFeeds [_A, _B]
>       (| (_Af, _Bf) |) 
>     D d :$ _ -> do
>       _Af <- eHope ("A" :<: (| SET |))
>       _A <- eLatest _Af
>       _Bf <- eHope ("B" :<: (| (exp _A --> SET) |))
>       _B <- eLatest _Bf
>       _T'f <- eFeed (PI (exp _A) (exp _B))
>       eInst (defName d, _Tf) (SET :>: _T'f) 
>       (| (_Af, _Bf) |)
>     _T -> error ("ePi: " ++ ugly V0 _T) 

> eSet :: Feed -> NewElab ()
> eSet _Tf = do
>   _T <- eLatest _Tf
>   case _T of 
>     SET -> (| () |)
>     D d :$ _ -> eFeed SET >>= \setf -> eInst (defName d, _Tf) (SET :>: setf)
>     x -> error (ugly V0 x)

> eDub' :: Template -> NewElab (Feed {- Thing -} :<: Feed {- Scheme -})
> eDub' t = do
>   x <- eDub t
>   case x of
>     Just y -> (| y |)
>     Nothing -> eCry [err ("Dubbing " ++ t ++ " failed")]

