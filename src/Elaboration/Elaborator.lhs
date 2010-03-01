\section{The Elaborator}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Elaboration.Elaborator where

> import Control.Applicative
> import Control.Monad.Error
> import Data.Traversable

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features ()

> import ProofState.Developments
> import ProofState.Lifting
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import Tactics.PropSimp

> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.Unification

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\subsection{Implementing the |Elab| monad}

The |runElab| proof state command actually interprets an |Elab x| in
the proof state. That is, it defines the semantics of the |Elab| syntax.
It returns |True| in the second component if elaboration was successful,
and |False| if the problem was suspended.

> runElab :: Bool -> (TY :>: Elab (INTM :=>: VAL))
>                       -> ProofState (INTM :=>: VAL, Bool)
> runElab _ (_ :>: Bale x) = return (x, True)

> runElab True (ty :>: ELambda x f) = case lambdable ty of
>     Just (_, s, tyf) -> do
>         ref <- lambdaBoy x
>         runElab True (tyf (NP ref) :>: f ref)
>     Nothing -> throwError' $ err "runElab: type" ++ errTyVal (ty :<: SET)
>                                  ++ err "is not lambdable!"

> runElab False (ty :>: ELambda s f) = runElabTop (ty :>: ELambda s f)

> runElab top (ty :>: EGoal f) = runElab top (ty :>: f ty)

> runElab top (ty :>: EHope tyHope f) = runElabHope tyHope
>     >>= runElab top . (ty :>:) . f

> runElab top (ty :>: EWait s tyWait f) = do
>     tyWait' <- bquoteHere tyWait
>     tt <- make' Waiting (s :<: tyWait' :=>: tyWait)
>     runElab top (ty :>: f tt)

> runElab top (ty :>: EElab l p f)  = runElabProb l p
>     >>= runElab top . (ty :>:) . f . fst

> runElab top (ty :>: ECompute (tyComp :>: elab) f) = runElabTop (tyComp :>: elab)
>     >>= runElab top . (ty :>:) . f . fst

> runElab True (ty :>: ECry e) = do
>     e' <- distillErrors e
>     let msg = show (prettyStackError e')
>     mn <- getMotherName
>     proofTrace ("Hole " ++ showName mn ++ " started crying:\n" ++ msg)
>     putHoleKind (Crying msg)
>     t :=>: tv <- getMotherDefinition
>     return (N t :=>: tv, False)

> runElab False (ty :>: ECry e) = runElabTop (ty :>: ECry e)

> runElab True (ty :>: EFake b f)           = do
>     GirlMother (nom := HOLE _ :<: ty) _ _ _ <- getMother
>     let fr = nom := FAKE :<: ty
>     xs <- if b  then  (| boySpine getAuncles |)
>                 else  (| (init . boySpine) getAuncles |)
>     let tm = P fr $:$ xs
>     runElab True . (ty :>:) . f $ tm :=>: evTm tm

> runElab False (ty :>: EFake b f) = runElabTop (ty :>: EFake b f)


> runElab top (ty :>: EResolve rn f) = do
>     (ref, as, ms) <- resolveHere rn
>     let tm = P ref $:$ as
>     (tmv :<: tyv) <- inferHere tm
>     tyv'  <- bquoteHere tyv
>     runElab top (ty :>: f (PAIR tyv' (N tm) :=>: PAIR tyv tmv, ms))
>   

> runElab top (ty :>: EQuote v f) = do
>     tm <- bquoteHere v
>     runElab top (ty :>: f (tm :=>: v))

> runElab top (ty :>: ECoerce (_S :=>: _Sv) (_T :=>: _Tv) (s :=>: sv) f) = do
>     eq <- withNSupply (equal $ SET :>: (_Sv, _Tv))
>     tt <- if eq
>         then return (s :=>: sv)
>         else do
>             q :=>: qv <- runElabHope (PRF (EQBLUE (SET :>: _Sv) (SET :>: _Tv)))
>             return $ N (coe :@ [_S, _T, q, s]) :=>: coe @@ [_Sv, _Tv, qv, sv]
>     runElab top (ty :>: f tt)

> runElab top (ty :>: tm) = throwError' . err $ "runElab: cannot evaluate "
>                                                 ++ show tm


The |runElabTop| command interprets the |Elab| monad at the top level, by
creating a new subgoal corresponding to the solution. This is necessary
when commands that need to modify the proof state (such as |ELambda|)
are encountered below the top level.

> runElabTop :: (TY :>: Elab (INTM :=>: VAL)) -> ProofState (INTM :=>: VAL, Bool)
> runElabTop (ty :>: elab) = do
>     ty' <- bquoteHere ty
>     x <- pickName "h" ""
>     make' Waiting (x :<: ty' :=>: ty)
>     goIn
>     (tm :=>: tmv, okay) <- runElab True (ty :>: elab)
>     if okay
>         then  return . (, True)  =<< neutralise =<< give tm
>         else  return . (, False) =<< neutralise =<< getMotherDefinition <* goOut


The |runElabHope| command interprets the |EHope| instruction, which hopes for
an element of a given type. If it is asking for a proof, we might be able to
find one, but otherwise we just create a hole.

> runElabHope :: TY -> ProofState (INTM :=>: VAL)
> runElabHope (PRF p)  = flexiProof p <|> simplifyProof p
> runElabHope ty       = lastHope ty

> lastHope :: TY -> ProofState (INTM :=>: VAL)
> lastHope ty = do
>     ty' <- bquoteHere ty
>     neutralise =<< make' Hoping ("hope" :<: ty' :=>: ty)

> flexiProof :: VAL -> ProofState (INTM :=>: VAL)
> flexiProof p@(EQBLUE (_S :>: s) (_T :>: (NP ref@(_ := HOLE Hoping :<: _)))) = do
>     s' <- bquoteHere s
>     _S' <- bquoteHere _S
>     _T' <- bquoteHere _T
>     let p' = EQBLUE (_S' :>: s') (_T' :>: NP ref)
>     neutralise =<< suspend ("hope" :<: PRF p' :=>: PRF p)
>         (WaitSolve ref (s' :=>: s) (ElabDone (N (P refl :$ A _S' :$ A s')
>                                               :=>: pval refl $$ A _S $$ A s)))

> flexiProof p@(EQBLUE (_T :>: (NP ref@(_ := HOLE Hoping :<: _))) (_S :>: s)) = do
>     s' <- bquoteHere s
>     _S' <- bquoteHere _S
>     _T' <- bquoteHere _T
>     let p' = EQBLUE (_T' :>: NP ref) (_S' :>: s')
>     neutralise =<< suspend ("hope" :<: PRF p' :=>: PRF p)
>         (WaitSolve ref (s' :=>: s) (ElabDone (N (P refl :$ A _S' :$ A s')
>                                               :=>: pval refl $$ A _S $$ A s)))

> flexiProof _ = (|)

> simplifyProof :: VAL -> ProofState (INTM :=>: VAL)
> simplifyProof p = do
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Just (SimplyTrivial prf) -> do
>             prf' <- bquoteHere prf
>             return $ prf' :=>: prf
>         Just (SimplyAbsurd _) -> return . fst =<< runElabTop (PRF p :>:
>             ECry [err "lastHope: proposition is absurd!"])
>         Just (Simply qs _ h) -> do
>             qrs <- Data.Traversable.mapM (subProof  . pty) qs
>             h' <- dischargeLots qs h
>             let prf = h' $$$ fmap (A . valueOf) qrs
>             prf' <- bquoteHere prf
>             return $ prf' :=>: prf
>         Nothing -> lastHope (PRF p)
>   where
>     subProof :: VAL -> ProofState (INTM :=>: VAL)
>     subProof (PRF p) = flexiProof p <|> lastHope (PRF p)


The |runElabProb| command interprets the |EElab| instruction, which holds a syntactic
representation of an elaboration problem. 
\question{How should this relate to the |internalElab| instruction?}

> runElabProb :: Loc -> (TY :>: EProb) -> ProofState (INTM :=>: VAL, Bool)
> runElabProb loc (ty :>: ElabDone tt) = return (tt, True)
> runElabProb loc (ty :>: ElabProb tm) = runElab False (ty :>: makeElab loc (ty :>: tm))
> runElabProb loc (ty :>: ElabInferProb tm) = runElab False (ty :>: makeElabInfer loc tm)
> runElabProb loc (ty :>: WaitCan (_ :=>: C _) prob) = runElabProb loc (ty :>: prob)
> runElabProb loc (ty :>: prob) = do
>     ty' <- bquoteHere ty
>     return . (, False) =<< neutralise =<< suspend (name prob :<: ty' :=>: ty) prob
>   where
>     name :: EProb -> String
>     name (WaitCan _ _)      = "can"
>     name (WaitSolve _ _ _)  = "solve"
>     name _                  = "suspend"


The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration problem to its tip.
When the scheduler hits the goal, the elaboration problem will restart if it
is unstable.

> suspend :: (String :<: INTM :=>: TY) -> EProb
>                -> ProofState (EXTM :=>: VAL)
> suspend (x :<: tt) prob = do
>     r <- make' Waiting (x :<: tt)
>     Just (E ref xn (Girl LETG (es, Unknown utt, nsupply) ms) tm) <- removeDevEntry
>     putDevEntry (E ref xn (Girl LETG (es, Suspended utt prob, nsupply) ms) tm)
>     return r


The |suspendMe| command attaches a suspended elaboration problem to the current
location.

> suspendMe :: EProb -> ProofState (EXTM :=>: VAL)
> suspendMe prob = do
>     Unknown tt <- getDevTip
>     putDevTip (Suspended tt prob)
>     getMotherDefinition



\subsection{Elaborating terms}

The |elaborate| command elaborates a term in display syntax, given its type,
to produce an elaborated term and its value representation. It behaves
similarly to |check| from subsection~\ref{subsec:type-checking}, except that
it operates in the |Elab| monad, so it can create subgoals and
$\lambda$-lift terms.

> elaborate :: Loc -> (TY :>: InDTmRN) -> ProofState (INTM :=>: VAL)
> elaborate loc (ty :>: tm) = runElab False (ty :>: makeElab loc (ty :>: tm))
>     >>= return . fst

> elaborate' = elaborate (Loc 0)


> elaborateHere :: Loc -> InDTmRN -> ProofState (INTM :=>: VAL)
> elaborateHere loc tm = do
>     _ :=>: ty <- getHoleGoal
>     return . fst =<< runElab True (ty :>: makeElab loc (ty :>: tm))

> elaborateHere' = elaborateHere (Loc 0)


> elabInfer :: Loc -> ExDTmRN -> ProofState (INTM :=>: VAL :<: TY)
> elabInfer loc tm = do
>     (tt, _) <- runElab False (sigSetVAL :>: makeElabInfer loc tm)
>     let (tt' :<: _ :=>: ty) = extractNeutral tt
>     return (tt' :<: ty)

> elabInfer' = elabInfer (Loc 0)



\subsection{Elaborated Construction Commands}


The |elabGive| command elaborates the given display term in the appropriate type for
the current goal, and calls the |give| command on the resulting term. If its argument
is a nameless question mark, it avoids creating a pointless subgoal by simply returning
a reference to the current goal (applied to the appropriate shared parameters).

> elabGive :: InDTmRN -> ProofState (EXTM :=>: VAL)
> elabGive tm = elabGive' tm <* goOut

> elabGiveNext :: InDTmRN -> ProofState (EXTM :=>: VAL)
> elabGiveNext tm = elabGive' tm <* (nextGoal <|> goOut)

> elabGive' :: InDTmRN -> ProofState (EXTM :=>: VAL)
> elabGive' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown _ -> do
>             case tm of
>                 DQ "" -> do
>                     GirlMother ref _ _ _ <- getMother
>                     aus <- getGreatAuncles
>                     return (applyAuncles ref aus)
>                 _ -> do
>                     tm' :=>: _ <- elaborateHere' tm
>                     give' tm'
>         _  -> throwError' $ err "elabGive: only possible for incomplete goals."


The |elabMake| command elaborates the given display term in a module to
produce a type, then converts the module to a goal with that type. Thus any
subgoals produced by elaboration will be children of the resulting goal.

> elabMake :: (String :<: InDTmRN) -> ProofState (EXTM :=>: VAL)
> elabMake (s :<: ty) = do
>     makeModule s
>     goIn
>     ty' :=>: _ <- elaborate' (SET :>: ty)
>     tm <- moduleToGoal ty'
>     goOutProperly
>     return tm


The |elabProgram| command adds a label to a type, given a list of arguments.
e.g. with a goal |plus : Nat -> Nat -> Nat|, |program x,y| will give a proof
state of:

\begin{verbatim}
plus [
  plus := ? : (x : Nat) -> (y : Nat) -> <plus x y : Nat>
  \ x : Nat
  \ y : Nat
] plus x y call : Nat
\end{verbatim}

> elabProgram :: [String] -> ProofState (EXTM :=>: VAL)
> elabProgram args = do
>     n <- getMotherName
>     (_ :=>: g) <- getHoleGoal
>     let pn = P (n := FAKE :<: g)
>     let newty = pity (mkTel pn g [] args)
>     newty' <- bquoteHere newty
>     g :=>: _ <- make (fst (last n) :<: newty') 
>     argrefs <- traverse lambdaBoy args
>     let fcall = pn $## (map NP argrefs) 
>     let call = g $## (map NP argrefs) :$ Call (N fcall)
>     r <- give' (N call)
>     goIn
>     return r
>   where mkTel :: NEU -> TY -> [VAL] -> [String] -> TEL TY
>         mkTel n (PI s t) args (x:xs)
>            = (x :<: s) :-: (\val -> mkTel n (t $$ A val) (val:args) xs)
>         mkTel n r args _ = Target (LABEL (mkL n (reverse args)) r)
>         
>         mkL :: NEU -> [VAL] -> VAL
>         mkL n [] = N n
>         mkL n (x:xs) = mkL (n :$ (A x)) xs


The |elabPiBoy| command elaborates the given display term to produce a type, and
creates a $\Pi$-boy with that type.

> elabPiBoy :: (String :<: InDTmRN) -> ProofState REF
> elabPiBoy (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     piBoy' (s :<: tt)

> elabLamBoy :: (String :<: InDTmRN) -> ProofState REF
> elabLamBoy (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     lambdaBoy' (s :<: tt)


\subsection{Elaborating Schemes}

> elabLet :: (String :<: Scheme InDTmRN) -> ProofState (EXTM :=>: VAL)
> elabLet (x :<: sch) = do
>     makeModule x
>     goIn
>     make ("tau" :<: SET)
>     goIn
>     (sch', ty :=>: _) <- elabScheme B0 sch
>     moduleToGoal (N ty)     
>     putMotherScheme sch'
>     r <- elabProgram (schemeNames sch')
>     putMotherScheme sch' -- this is wrong but does it matter?
>     return r


> elabScheme :: Entries -> Scheme InDTmRN -> ProofState (Scheme INTM, EXTM :=>: VAL)

> elabScheme es (SchType ty) = do
>     ty' :=>: _ <- elaborate' (SET :>: ty)
>     tt <- give ty'
>     return (SchType (es -| ty'), tt)

> elabScheme es (SchExplicitPi (x :<: s) t) = do
>     make ("tau" :<: SET)
>     goIn
>     (s', ty :=>: _) <- elabScheme es s
>     piBoy (x :<: N ty)
>     e <- getDevEntry
>     (t', tt) <- elabScheme (es :< e) t
>     return (SchExplicitPi (x :<: s') t', tt)

> elabScheme es (SchImplicitPi (x :<: s) t) = do
>     ss <- elaborate' (SET :>: s)
>     piBoy (x :<: termOf ss)
>     e <- getDevEntry
>     (t', tt) <- elabScheme (es :< e) t
>     return (SchImplicitPi (x :<: (es -| termOf ss)) t', tt)