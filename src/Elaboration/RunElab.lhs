\section{Implementing the |Elab| monad}
\label{sec:run_elab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.RunElab where

> import Control.Applicative
> import Control.Monad.Error
> import Data.Traversable

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features ()

> import ProofState.Developments
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.Naming

> import Tactics.PropSimp

> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.Unification

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\subsection{Running elaboration processes}

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

> runElab top (ty :>: EWait s tyWait f) = do
>     tyWait' <- bquoteHere tyWait
>     tt <- make' Waiting (s :<: tyWait' :=>: tyWait)
>     runElab top (ty :>: f tt)

> runElab top (ty :>: EElab l p)  = runElabProb top l (ty :>: p)

> runElab top (ty :>: ECompute (tyComp :>: elab) f) = runElab False (tyComp :>: elab)
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

> runElab top (ty :>: EAskNSupply f) = do
>     nsupply <- askNSupply
>     runElab top (ty :>: f nsupply)


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


\subsection{Interpreting elaboration problems}

The |runElabProb| command interprets the |EElab| instruction, which holds a syntactic
representation of an elaboration problem. 

> runElabProb :: Bool -> Loc -> (TY :>: EProb) -> ProofState (INTM :=>: VAL, Bool)
> runElabProb top loc (ty :>: ElabDone tt)  = return (maybeEval tt, True)
> runElabProb top loc (ty :>: ElabHope)     = runElabHope top ty
> runElabProb top loc (ty :>: ElabProb tm)  = runElab top (ty :>: makeElab loc tm)
> runElabProb top loc (ty :>: ElabInferProb tm) =
>     runElab top (ty :>: makeElabInfer loc tm)
> runElabProb top loc (ty :>: WaitCan (_ :=>: Just (C _)) prob) =
>     runElabProb top loc (ty :>: prob)
> runElabProb top loc (ty :>: WaitCan (tm :=>: Nothing) prob) =
>     runElabProb top loc (ty :>: WaitCan (tm :=>: Just (evTm tm)) prob)
> runElabProb top loc (ty :>: prob) = do
>     ty' <- bquoteHere ty
>     suspendThis top (name prob :<: ty' :=>: ty) prob
>   where
>     name :: EProb -> String
>     name (WaitCan _ _)      = "can"
>     name (WaitSolve _ _ _)  = "solve"
>     name _                  = "suspend"

\subsection{Hoping, hoping, hoping}

The |runElabHope| command interprets the |EHope| instruction, which hopes for
an element of a given type. If it is asking for an element of unit, a proof
or an element of a labelled type, we might be able to find one; otherwise we
just create a hole.

> runElabHope :: Bool -> TY -> ProofState (INTM :=>: VAL, Bool)
> runElabHope top UNIT                = return (VOID :=>: VOID, True)
> runElabHope top (PRF p)             = simplifyProof top p
> runElabHope top v@(LABEL (N l) ty)  = seekLabel top l ty <|> lastHope top v
> runElabHope top ty                  = lastHope top ty


\subsubsection{Hoping for labelled types}

If we are looking for a labelled type (e.g.\ to make a recursive call), we
search the hypotheses for a value with the same label.

> seekLabel :: Bool -> NEU -> VAL -> ProofState (INTM :=>: VAL, Bool)
> seekLabel top l ty = do
>     es <- getAuncles
>     seekOn es
>   where
>     seekOn B0                             =    (|)
>     seekOn (es' :< E boy _ (Boy LAMB) _)  =    seekIn (NP boy) (pty boy)
>                                           <|>  seekOn es'
>     seekOn (es' :< _)                     =    seekOn es'

>     seekIn :: VAL -> VAL -> ProofState (INTM :=>: VAL, Bool)
>     seekIn tm (LABEL (N m) u) = do
>         let Just (ref, vvs) = matchFakes m l []
>         subst  <- matchBits (pty ref) vvs [] 
>         l'     <- bquoteHere l
>         ty'    <- bquoteHere ty
>         tm'    <- bquoteHere tm
>         suspendThis top ("label" :<: LABEL (N l') ty' :=>: LABEL (N l) ty) =<<
>             makeWait subst tm'
>     seekIn tm (PI s t) = do
>         (st :=>: sv, _) <- runElabHope False s    
>         seekIn (tm $$ A sv) (t $$ A sv)
>     seekIn tm ty = (|)

>     matchBits :: TY -> [(VAL, VAL)] -> [(REF, VAL)]
>         -> ProofState [(REF, VAL)]
>     matchBits ty [] subst = return subst
>     matchBits (PI s t) ((as, at):ps) subst = do
>         subst' <- valueMatch (s :>: (as, at))
>         matchBits (t $$ A as) ps (subst ++ subst')


> matchFakes :: NEU -> NEU -> [(VAL, VAL)] -> Maybe (REF, [(VAL, VAL)])
> matchFakes (P ref@(sn := FAKE :<: _)) (P (tn := FAKE :<: _)) ps
>     | sn == tn   = Just (ref, ps)
>     | otherwise  = Nothing
> matchFakes (s :$ A as) (t :$ A at) ps = matchFakes s t ((as, at):ps)
> matchFakes _ _ _ = Nothing 

> makeWait :: [(REF, VAL)] -> INTM -> ProofState EProb
> makeWait [] g = return $ ElabDone (g :=>: Nothing)
> makeWait ((r, v) : rvs) g = do
>     v' <- bquoteHere v
>     ep <- makeWait rvs g
>     return $ WaitSolve r (v' :=>: Just v) ep


\subsubsection{Simplifying proofs}

If we are hoping for a proof of a proposition, we first try simplifying it using
the propositional simplification machinery.

> simplifyProof :: Bool -> VAL -> ProofState (INTM :=>: VAL, Bool)
> simplifyProof top p = do
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Just (SimplyTrivial prf) -> do
>             prf' <- bquoteHere prf
>             return (prf' :=>: prf, True)
>         Just (SimplyAbsurd _) -> runElab top (PRF p :>:
>             ECry [err "simplifyProof: proposition is absurd:"
>                          ++ errTyVal (p :<: PROP)])
>         Just (Simply qs _ h) -> do
>             qrs <- Data.Traversable.mapM partProof qs
>             h' <- dischargeLots qs h
>             let prf = h' $$$ qrs
>             prf' <- bquoteHere prf
>             return (prf' :=>: prf, True)
>         Nothing -> subProof top (PRF p)
>   where
>     partProof :: REF -> ProofState (Elim VAL)
>     partProof ref = return . A . valueOf . fst =<< subProof False (pty ref)

>     subProof :: Bool -> VAL -> ProofState (INTM :=>: VAL, Bool)
>     subProof top (PRF p) = flexiProof top p <|> lastHope top (PRF p)


After simplification has dealt with the easy stuff, it calls |flexiProof| to
solve any flex-rigid equations (by suspending a solution process on a subgoal
and returning the subgoal). 

> flexiProof :: Bool -> VAL -> ProofState (INTM :=>: VAL, Bool)

> flexiProof top (EQBLUE (_S :>: s) (_T :>: t)) = 
>     flexiProofMatch           (_S :>: s) (_T :>: t)
>     <|> flexiProofLeft   top  (_S :>: s) (_T :>: t)
>     <|> flexiProofRight  top  (_S :>: s) (_T :>: t)
> flexiProof _ _ = (|)

If we are trying to prove an equation between the same fake reference applied to
two lists of parameters, we prove equality of the parameters and use reflexivity.
This case arises frequently when proving label equality to make recursive calls.
\question{Do we need this case, or are we better off using matching?}

> flexiProofMatch :: (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, Bool)
> flexiProofMatch (_S :>: N s) (_T :>: N t)
>   | Just (ref, ps) <- matchFakes s t [] = do
>     let ty = pty ref
>     prfs <- proveBits ty ps B0
>     let  q  = NP refl $$ A ty $$ A (NP ref) $$ Out
>          r  = CON (smash q (trail prfs))
>     r' <- bquoteHere r
>     return (r' :=>: r, True)
>   where
>     proveBits :: TY -> [(VAL, VAL)] -> Bwd (VAL, VAL, VAL)
>         -> ProofState (Bwd (VAL, VAL, VAL))
>     proveBits ty [] prfs = return prfs
>     proveBits (PI s t) ((as, at):ps) prfs = do
>         (_ :=>: prf, _) <- simplifyProof False (EQBLUE (s :>: as) (s :>: at))
>         proveBits (t $$ A as) ps (prfs :< (as, at, prf))

>     smash :: VAL -> [(VAL, VAL, VAL)] -> VAL
>     smash q [] = q
>     smash q ((as, at, prf):ps) = smash (q $$ A as $$ A at $$ A prf) ps

> flexiProofMatch _ _ = (|)

If one side of the equation is a hoping hole applied to the shared parameters of
our current location, we can solve it with the other side of the equation.
\question{How can we generalise this to cases where the hole is under a different
list of parameters?}

\question{Can we hope for a proof of equality and
insert a coercion rather than demanding definitional equality of the sets?
See Elab.pig for an example where this makes the elaboration process fragile,
because we end up trying to move definitions with processes attached.}

> flexiProofLeft :: Bool -> (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, Bool)
> flexiProofLeft top (_T :>: N t) (_S :>: s) = do
>     guard =<< withNSupply (equal (SET :>: (_S, _T)))

<     (q' :=>: q, _) <- simplifyProof False (EQBLUE (SET :>: _S) (SET :>: _T))

>     ref  <- stripShared t
>     s'   <- bquoteHere s
>     _S'  <- bquoteHere _S
>     t'   <- bquoteHere t
>     _T'  <- bquoteHere _T
>     let  p      = EQBLUE (_T   :>: N t   ) (_S   :>: s   )
>          p'     = EQBLUE (_T'  :>: N t'  ) (_S'  :>: s'  )

<          N (coe :@ [_S', _T', q', s']) :=>: Just (coe @@ [_S, _T, q, s])

>          eprob  = (WaitSolve ref (s' :=>: Just s)
>                      (ElabDone (N (P refl :$ A _S' :$ A s')
>                           :=>: Just (pval refl $$ A _S $$ A s))))
>     suspendThis top ("eq" :<: PRF p' :=>: PRF p) eprob
> flexiProofLeft _ _ _ = (|)



> flexiProofRight :: Bool -> (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, Bool)
> flexiProofRight top (_S :>: s) (_T :>: N t) = do
>     guard =<< withNSupply (equal (SET :>: (_S, _T)))
>     ref  <- stripShared t
>     s'   <- bquoteHere s
>     _S'  <- bquoteHere _S
>     t'   <- bquoteHere t
>     _T'  <- bquoteHere _T
>     let  p      = EQBLUE (_S   :>: s   ) (_T   :>: N t   )
>          p'     = EQBLUE (_S'  :>: s'  ) (_T'  :>: N t'  )
>          eprob  = (WaitSolve ref (s' :=>: Just s)
>                      (ElabDone (N (P refl :$ A _S' :$ A s')
>                           :=>: Just (pval refl $$ A _S $$ A s))))
>     suspendThis top ("eq" :<: PRF p' :=>: PRF p) eprob
> flexiProofRight _ _ _ = (|)




If all else fails, we can hope for anything we like by creating a subgoal, though
ideally we should cry rather than hoping for something patently absurd.

> lastHope :: Bool -> TY -> ProofState (INTM :=>: VAL, Bool)
> lastHope True ty = do
>     putHoleKind Hoping
>     return . (, False) =<< neutralise =<< getMotherDefinition
> lastHope False ty = do
>     ty' <- bquoteHere ty
>     return . (, True) =<< neutralise =<< make' Hoping ("hope" :<: ty' :=>: ty)


\subsection{Suspending computation}

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


The |suspendThis| command attaches the problem to the current hole if the
top-level boolean is |True|, and creates a new subgoal otherwise.

> suspendThis :: Bool -> (String :<: INTM :=>: TY) -> EProb
>     -> ProofState (INTM :=>: VAL, Bool)
> suspendThis True   _    ep = return . (, False)  =<< neutralise =<< suspendMe ep
> suspendThis False  stt  ep = return . (, True)   =<< neutralise =<< suspend stt ep