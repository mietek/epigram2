\section{Implementing the |Elab| monad}
\label{sec:Elaborator.RunElab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.RunElab where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Traversable

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality
> import Evidences.Utilities

> import Features.Features ()

> import ProofState.Structure.Developments

> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.FakeRef

> import ProofState.Interface.ProofKit
> import ProofState.Interface.NameResolution
> import ProofState.Interface.Name
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import ProofState.Interface.Solving

> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import Tactics.PropositionSimplify
> import Tactics.Matching
> import Tactics.Unification

> import Elaboration.ElabProb
> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.Wire

> import Distillation.Distiller

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace

%endif

\subsection{Running elaboration processes}
\label{subsec:Elaborator.RunElab.runElab}

The |runElab| proof state command actually interprets an |Elab x| in
the proof state. In other words, we define here the semantics of the
|Elab| syntax.

> runElab :: WorkTarget ->  (TY :>: Elab (INTM :=>: VAL)) -> 
>                           ProofState (INTM :=>: VAL, ElabStatus)

This command is given a type and a program in the |Elab| DSL for creating an
element of that type. It is also given a flag indicating whether elaboration
is working on the current goal in the proof state. If the target is the current
goal, the type pushed in must match the type of the goal. 

> data WorkTarget = WorkCurrentGoal | WorkElsewhere

It will return the term produced by elaboration, and a flag indicating whether
elaboration was completely successful or had to suspend. If elaboration
suspended when working on the curent goal, the term will be a reference to that
goal, so it cannot be solved.

> data ElabStatus = ElabSuccess | ElabSuspended deriving Eq

Some |Elab| instructions can only be used when working on the current goal,
for example introducting a lambda. We identify these so we can make a new
subgoal when trying to execute them elsewhere.

> currentGoalOnly :: Elab x -> Bool
> currentGoalOnly (ELambda _ _)  =  True
> currentGoalOnly (ECry _)       =  True
> currentGoalOnly (EFake _)      =  True
> currentGoalOnly (EAnchor _)    =  True
> currentGoalOnly _              =  False


Now, let us give the semantics of each command in turn. First of all,
we catch all commands that can only run on the current goal,
and redirect them to the specially crafted |runElabNewGoal|.

> runElab WorkElsewhere (ty :>: elab) | currentGoalOnly elab = runElabNewGoal (ty :>: elab)

|EReturn| is the @return@ of the monad. It does nothing and always succeeds.

> runElab _ (_ :>: EReturn x) = return (x, ElabSuccess)

|ELambda| creates a \(\lambda\)-parameter, if this is allowed by the
type we are elaborating to.

> runElab WorkCurrentGoal (ty :>: ELambda x f) = case lambdable ty of
>     Just (_, s, tyf) -> do
>         ref <- lambdaParam x
>         runElab WorkCurrentGoal (tyf (NP ref) :>: f ref)
>     Nothing -> throwError' $ err "runElab: type" ++ errTyVal (ty :<: SET)
>                                  ++ err "is not lambdable!"

|EGoal| retrieves the current goal and passes it to the elaboration task.

> runElab wrk (ty :>: EGoal f) = runElab wrk (ty :>: f ty)

|EWait| makes a |Waiting| hole and pass it along to the next elaboration task.

> runElab wrk (ty :>: EWait s tyWait f) = do
>     tyWait' <- bquoteHere tyWait
>     tt <- make (s :<: tyWait')
>     runElab wrk (ty :>: f tt)

|EElab| contains a syntactic representation of an elaboration problem. This
representation is interpreted and executed by |runElabProb|.

> runElab wrk (ty :>: EElab l p)  = runElabProb wrk l (ty :>: p)

|ECompute| allows us to combine elaboration tasks: we run a first task
 and pass its result to the next elaboration task.

> runElab top (ty :>: ECompute (tyComp :>: elab) f) = do
>     (e , _) <- runElab WorkElsewhere (tyComp :>: elab) 
>     runElab top (ty :>: f e)

|ECry| is used to report an error. It updates the current entry into a
 crying state.

> runElab WorkCurrentGoal (ty :>: ECry e) = do
>     e' <- distillErrors e
>     let msg = show (prettyStackError e')
>     mn <- getCurrentName
>     elabTrace $ "Hole " ++ showName mn ++ " started crying:\n" ++ msg
>     putHoleKind (Crying msg)
>     t :=>: tv <- getCurrentDefinition
>     return (N t :=>: tv, ElabSuspended)

|EFake| extracts the reference of the current entry and presents it as
 a fake reference. \pierre{This is an artifact of our current
 implementation of labels, this should go away when we label
 high-level objects with high-level names}.

> runElab WorkCurrentGoal (ty :>: EFake f) = do
>     r <- getFakeRef 
>     inScope <- getInScope
>     runElab WorkCurrentGoal . (ty :>:) $ f (r, paramSpine inScope)

|EAnchor| extracts the name of the current entry.

> runElab WorkCurrentGoal (ty :>: EAnchor f) = do
>     name <- getCurrentName
>     runElab WorkCurrentGoal . (ty :>:) $ f (fst (last name))


|EResolve| provides a name-resolution service: given a relative name,
 it finds the term and potentially the scheme of the definition the
 name refers to. This is passed onto the next elaboration task.

> runElab wrk (ty :>: EResolve rn f) = do
>     (ref, as, ms) <- resolveHere rn
>     let  tm   = P ref $:$ toSpine as
>          ms'  = (| (flip applyScheme as) ms |)
>     (tmv :<: tyv) <- inferHere tm
>     tyv'  <- bquoteHere tyv
>     runElab wrk (ty :>: f (PAIR tyv' (N tm) :=>: PAIR tyv tmv, ms'))
>   

|EAskNSupply| gives access to the name supply to the next elaboration
 task.

\begin{danger}[Read-only name supply]

As often, we are giving here a read-only access to the name
supply. Therefore, we must be careful not to let some generated names
dangling into some definitions, or clashes could happen.

\end{danger}

> runElab wrk (ty :>: EAskNSupply f) = do
>     nsupply <- askNSupply
>     runElab wrk (ty :>: f nsupply)


As mentioned above, some commands can only be used when elaboration is taking
place in the current goal. This is the purpose of |runElabNewGoal|: it creates
a dummy definition and hands back the elaboration task to |runElab|.

> runElabNewGoal :: (TY :>: Elab (INTM :=>: VAL)) -> ProofState (INTM :=>: VAL, ElabStatus)
> runElabNewGoal (ty :>: elab) = do
>     -- Make a dummy definition
>     ty' <- bquoteHere ty
>     x <- pickName "h" ""
>     make (x :<: ty')
>     -- Enter its development
>     goIn
>     (tm :=>: tmv, status) <- runElab WorkCurrentGoal (ty :>: elab)
>     -- Leave the development, one way or the other
>     case status of
>       ElabSuccess -> do
>                 -- By finalising it
>                 t <- giveOutBelow tm
>                 e <- neutralise t
>                 return (e , ElabSuccess)
>       ElabSuspended -> do
>                 -- By leaving it unfinished
>                 currentDef <- getCurrentDefinition
>                 e <- neutralise currentDef
>                 goOut
>                 return (e , ElabSuspended)


\subsection{Interpreting elaboration problems}

The |runElabProb| interprets the syntactic representation of an
elaboration problem. In other words, this function defines the
semantics of the |EProb| language.

> runElabProb :: WorkTarget ->  Loc -> (TY :>: EProb) -> 
>                               ProofState (INTM :=>: VAL, ElabStatus)

|ElabDone tt| always succeed at returning the given term |tt|.

> runElabProb wrk loc (ty :>: ElabDone tt)  = 
>     return (maybeEval tt, ElabSuccess)

|ElabProb tm| asks for the elaboration of the display term |tm| (for
 pushed-in terms).

> runElabProb wrk loc (ty :>: ElabProb tm)  =
>     runElab wrk (ty :>: makeElab loc tm)

|ElabInferProb tm| asks for the elaboration and type inference of the
 display term |tm| (for pull-out terms).

> runElabProb wrk loc (ty :>: ElabInferProb tm) =
>     runElab wrk (ty :>: makeElabInfer loc tm)

|WaitCan tm prob| prevents the interpretation of the elaboration
 problem |prob| until |tm| is indeed a canonical
 object. Otherwise, the problem is indefinitely suspended.

\pierre{This fall-through pattern-match reminds me of Duff's devices.}

> runElabProb wrk loc (ty :>: WaitCan (_ :=>: Just (C _)) prob) =
>     runElabProb wrk loc (ty :>: prob)
> runElabProb wrk loc (ty :>: WaitCan (tm :=>: Nothing) prob) =
>     runElabProb wrk loc (ty :>: WaitCan (tm :=>: Just (evTm tm)) prob)

The semantics of the |ElabHope| command is specifically given by the
|runElabHope| interpreter in
Section~\ref{subsec:Elaboration.RunElab.elabHope}.

> runElabProb wrk loc (ty :>: ElabHope)     = runElabHope wrk ty

Any case that has not matched yet ends in a suspended state: we cannot
make progress on it right now. The suspension of an elaboration
problem is decribed in details in
Section~\label{subsec:Elaboration.RunElab.suspending}. Once in a
suspended state, an elaboration problem might receive some care from
the Scheduler (Section~\ref{sec:Elaboration.Scheduler}), which might
be able to make some progress.

The following problems are suspended, for different reasons:
\begin{itemize}

\item a |WaitCan| command offering an object that is \emph{not}
canonical;

\item a |WaitSolve| command, because we cannot solve references during
elaboration, but the scheduler can do so later; and

\item an |ElabSchedule| command, whose purpose is to suspend the
current elaboration and call the scheduler.

\end{itemize}

\pierre{These are 3 different cases, getting suspended for 3 different
reasons. Maybe it's ok, but maybe suspension is being abused. If not,
there must be a nice way to present suspension that covers these 3
cases.}

> runElabProb top loc (ty :>: prob) = do
>     ty' <- bquoteHere ty
>     suspendThis top (name prob :<: ty' :=>: ty) prob
>   where
>     name :: EProb -> String
>     name (WaitCan _ _)      = "can"
>     name (WaitSolve _ _ _)  = "solve"
>     name (ElabSchedule _)   = "suspend"
>     name _                  = error "runElabProb: unexpected suspension."


\subsection{Hoping, hoping, hoping}
\label{subsec:Elaboration.RunElab.elabHope}

The |runElabHope| command interprets the |ElabHope| instruction, which
hopes for an element of a given type. In a few cases, based on the
type, we might be able to solve the problem immediately:
\begin{itemize}

\item An element of type |UNIT| is |VOID|;

\item A proof of a proposition might be found or refined by the
propositional simplifier
(Section~\ref{sec:Tactics.PropositionSimplify}); and

\item The solution of a programming is often an induction hypothesis
that is sitting in our context

\end{itemize}

If these strategies do not match or fail to solve the problem, we just
create a hole.

> runElabHope :: WorkTarget -> TY -> ProofState (INTM :=>: VAL, ElabStatus)
> runElabHope wrk UNIT                = return (VOID :=>: VOID, ElabSuccess)
> runElabHope wrk (PRF p)             = simplifyProof wrk p
> runElabHope wrk v@(LABEL (N l) ty)  = seekLabel wrk l ty <|> lastHope wrk v
> runElabHope wrk ty                  = lastHope wrk ty


\subsubsection{Hoping for labelled types}

If we are looking for a labelled type (e.g.\ to make a recursive call), we
search the hypotheses for a value with the same label.

> seekLabel :: WorkTarget -> NEU -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
> seekLabel wrk label ty = do
>     es <- getInScope
>     seekOn es
>     where

The traversal of the hypotheses is carried by |seekOn|. It searches
parameters and hands them to |seekIn|.

>       seekOn B0                                    = do
>           label' <- bquoteHere label
>           s <- prettyHere (ty :>: N label')
>           proofTrace $ "Failed to resolve recursive call to "
>                            ++ renderHouseStyle s
>           (|)
>       seekOn (es' :< EPARAM param _ ParamLam _ _)  = 
>           seekIn B0 (P param) (pty param) <|> seekOn es'
>       seekOn (es' :< _)                            =    seekOn es'

Then, |seekIn| tries to match the label we are looking for with an
hypothesis we have found. Recall that a label is a telescope
targetting a label, hence we try to peel off this telescope to match
the label. 

>       seekIn :: Bwd REF -> EXTM -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)

On our way to the label, we instantiate the hypotheses with fresh references.

>       seekIn rs tm (PI s t) = freshRef (fortran t :<: s) $ \ sRef ->
>           seekIn (rs :< sRef) (tm :$ A (NP sRef)) (t $$ A (pval sRef))

We might have to go inside branches (essentially finite $\Pi$-types).

>       seekIn rs tm (N (op :@ [e, p])) | op == branchesOp =
>           freshRef (fortran p :<: e) $ \ eRef -> do
>               e' <- bquoteHere e
>               p' <- bquoteHere p
>               seekIn (rs :< eRef) (switchOp :@ [e', NP eRef, p', N tm])
>                   (p $$ A (pval eRef))

We have reached a label! The question is then ``is this the one we are looking
for?'' First we call on the matcher (see section~\ref{subsec:Tactics.Matching})
to find values for the fresh references, then we generate a substitution from
these values and apply it to the call term.

>       seekIn rs tm (LABEL (N foundLabel) u) = do
>           ss <- execStateT (matchNeutral B0 foundLabel label) (fmap (, Nothing) rs)
>           (xs, vs)  <- processSubst ss
>           let c = substitute xs vs (N tm)
>           return (c :=>: evTm c, ElabSuccess)

If, in our way to the label the peeling fails, then we must give up.

>       seekIn rs tm ty = (|)


To generate a substitution, we quote the value given to each reference and
substitute out the preceding references. If a reference has no value, i.e. it
is unconstrained by the matching problem, we hope for a solution.
\adam{we could do some dependency analysis here to avoid cluttering the proof
state with hopes that we don't make use of.}

>       processSubst :: MatchSubst -> ProofState (Bwd (REF :<: INTM), Bwd INTM)
>       processSubst B0            = return (B0, B0)
>       processSubst (rs :< (r, Just t))  = do
>           (xs, vs)  <- processSubst rs
>           ty        <- bquoteHere (pty r)
>           tm        <- bquoteHere t
>           return (xs :< (r :<: substitute xs vs ty), vs :< substitute xs vs tm)
>       processSubst (rs :< (r, Nothing))  = do
>           (xs, vs)  <- processSubst rs
>           ty        <- bquoteHere (pty r)
>           let ty' = substitute xs vs ty
>           (tm :=>: _, _)  <- runElabHope WorkElsewhere (evTm ty')
>           return (xs :< (r :<: ty'), vs :< tm)


\subsubsection{Simplifying proofs}
\label{subsubsec:Elaboration.RunElab.proofs}

\pierre{To be reviewed.}

If we are hoping for a proof of a proposition, we first try simplifying it using
the propositional simplification machinery.

> simplifyProof :: WorkTarget -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
> simplifyProof wrk p = do
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Just (SimplyTrivial prf) -> do
>             return (prf :=>: evTm prf, ElabSuccess)
>         Just (SimplyAbsurd _) -> runElab wrk (PRF p :>:
>             ECry [err "simplifyProof: proposition is absurd:"
>                          ++ errTyVal (p :<: PROP)])
>         Just (Simply qs _ h) -> do
>             qrs <- traverse partProof qs
>             let prf = substitute qs qrs h
>             return (prf :=>: evTm prf, ElabSuccess)
>         Nothing -> subProof wrk (PRF p)
>   where
>     partProof :: (REF :<: INTM) -> ProofState INTM
>     partProof (ref :<: _) = do
>       ((tm :=>: _) , _) <- subProof WorkElsewhere (pty ref)
>       return tm

>     subProof :: WorkTarget -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
>     subProof wrk (PRF p) = flexiProof wrk p <|> lastHope wrk (PRF p)


After simplification has dealt with the easy stuff, it calls |flexiProof| to
solve any flex-rigid equations (by suspending a solution process on a subgoal
and returning the subgoal). 

> flexiProof :: WorkTarget -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)

> flexiProof wrk (EQBLUE (_S :>: s) (_T :>: t)) = 
>     flexiProofMatch           (_S :>: s) (_T :>: t)
>     <|> flexiProofLeft   wrk  (_S :>: s) (_T :>: t)
>     <|> flexiProofRight  wrk  (_S :>: s) (_T :>: t)
> flexiProof _ _ = (|)

If we are trying to prove an equation between the same fake reference applied to
two lists of parameters, we prove equality of the parameters and use reflexivity.
This case arises frequently when proving label equality to make recursive calls.
\question{Do we need this case, or are we better off using matching?}

> flexiProofMatch :: (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, ElabStatus)
> flexiProofMatch (_S :>: N s) (_T :>: N t)
>   | Just (ref, ps) <- pairSpines s t [] = do
>     let ty = pty ref
>     prfs <- proveBits ty ps B0
>     let  q  = NP refl $$ A ty $$ A (NP ref) $$ Out
>          r  = CON (smash q (trail prfs))
>     r' <- bquoteHere r
>     return (r' :=>: r, ElabSuccess)
>   where
>     pairSpines :: NEU -> NEU -> [(VAL, VAL)] -> Maybe (REF, [(VAL, VAL)])
>     pairSpines (P ref@(sn := _ :<: _)) (P (tn := _ :<: _)) ps
>       | sn == tn   = Just (ref, ps)
>       | otherwise  = Nothing
>     pairSpines (s :$ A as) (t :$ A at) ps = pairSpines s t ((as, at):ps)
>     pairSpines _ _ _ = Nothing 

>     proveBits :: TY -> [(VAL, VAL)] -> Bwd (VAL, VAL, VAL)
>         -> ProofState (Bwd (VAL, VAL, VAL))
>     proveBits ty [] prfs = return prfs
>     proveBits (PI s t) ((as, at):ps) prfs = do
>         (_ :=>: prf, _) <- simplifyProof WorkElsewhere (EQBLUE (s :>: as) (s :>: at)) 
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

> flexiProofLeft :: WorkTarget -> (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, ElabStatus)
> flexiProofLeft wrk (_T :>: N t) (_S :>: s) = do
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

>          eprob  = WaitSolve ref (s' :=>: Just s) ElabHope

>     suspendThis wrk ("eq" :<: PRF p' :=>: PRF p) eprob
> flexiProofLeft _ _ _ = (|)



> flexiProofRight :: WorkTarget -> (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, ElabStatus)
> flexiProofRight wrk (_S :>: s) (_T :>: N t) = do
>     guard =<< withNSupply (equal (SET :>: (_S, _T)))
>     ref  <- stripShared t
>     s'   <- bquoteHere s
>     _S'  <- bquoteHere _S
>     t'   <- bquoteHere t
>     _T'  <- bquoteHere _T
>     let  p      = EQBLUE (_S   :>: s   ) (_T   :>: N t   )
>          p'     = EQBLUE (_S'  :>: s'  ) (_T'  :>: N t'  )
>          eprob  = WaitSolve ref (s' :=>: Just s) ElabHope
>     suspendThis wrk ("eq" :<: PRF p' :=>: PRF p) eprob
> flexiProofRight _ _ _ = (|)




If all else fails, we can hope for anything we like by leaving a hoping
subgoal, either using the current one (if we are working on it) or creating a
new subgoal. Ideally we should cry rather than hoping for something
patently absurd: at the moment we reject some impossible hopes but do not
always spot them.

> lastHope :: WorkTarget -> TY -> ProofState (INTM :=>: VAL, ElabStatus)
> lastHope WorkCurrentGoal ty = do
>     putHoleKind Hoping
>     return . (, ElabSuspended) =<< neutralise =<< getCurrentDefinition
> lastHope WorkElsewhere ty = do
>     ty' <- bquoteHere ty
>     return . (, ElabSuccess) =<< neutralise =<< makeKinded Nothing Hoping ("hope" :<: ty')


\subsection{Suspending computation}
\label{subsec:Elaboration.RunElab.suspending}

\pierre{To be reviewed.}

The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration problem to its tip.
When the scheduler hits the goal, the elaboration problem will restart if it
is unstable.

> suspend :: (String :<: INTM :=>: TY) -> EProb -> ProofState (EXTM :=>: VAL)
> suspend (x :<: tt) prob = do
>     -- Make a hole
>     r <- make (x :<: termOf tt)
>     -- Store the suspended problem
>     Just (EDEF ref xn dkind dev@(Dev {devTip=Unknown utt}) tm anchor) <- removeEntryAbove
>     putEntryAbove (EDEF ref xn dkind (dev{devTip=Suspended utt prob}) tm anchor)
>     -- Mark the Suspension state
>     let ss = if isUnstable prob then SuspendUnstable else SuspendStable
>     putDevSuspendState ss
>     -- Mark for Scheduler action \pierre{right?}
>     suspendHierarchy ss
>     return r


The |suspendMe| command attaches a suspended elaboration problem to
the current location. \pierre{We expect the tip to be in an |Unknown|
state. That's an invariant.}

> suspendMe :: EProb -> ProofState (EXTM :=>: VAL)
> suspendMe prob = do
>     -- Store the suspended problem in the Tip
>     Unknown tt <- getDevTip
>     putDevTip (Suspended tt prob)
>     -- Mark for Scheduler action \pierre{right?}
>     let ss = if isUnstable prob then SuspendUnstable else SuspendStable
>     suspendHierarchy ss
>     getCurrentDefinition


The |suspendThis| command attaches the problem to the current goal if
we are working on it, and creates a new subgoal otherwise.

> suspendThis :: WorkTarget ->  (String :<: INTM :=>: TY) -> EProb -> 
>                               ProofState (INTM :=>: VAL, ElabStatus)
> suspendThis WorkCurrentGoal _ ep  = 
>     return . (, ElabSuspended)  =<< neutralise =<< suspendMe ep
> suspendThis WorkElsewhere  stt  ep = 
>     return . (, ElabSuccess)    =<< neutralise =<< suspend stt ep
