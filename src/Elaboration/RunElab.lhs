\section{Implementing the |Elab| monad}
\label{sec:Elaborator.RunElab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.RunElab where

> import Prelude hiding (foldl, exp)

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Traversable

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

> import Elaboration.ElabProb
> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.Wire

> import Distillation.Distiller

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace
> import Kit.NatFinVec


%endif

\subsection{Running elaboration processes}
\label{subsec:Elaborator.RunElab.runElab}

The |runElab| proof state command actually interprets an |Elab x| in
the proof state. In other words, we define here the semantics of the
|Elab| syntax.

> runElab :: WorkTarget ->  (TY :>: Elab EXP) -> 
>                           ProofState (EXP, ElabStatus)

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

< currentGoalOnly (EAnchor _)    =  True

> currentGoalOnly _              =  False


Now, let us give the semantics of each command in turn. First of all,
we catch all commands that can only run on the current goal,
and redirect them to the specially crafted |runElabNewGoal|.

> runElab WorkElsewhere (ty :>: elab) | currentGoalOnly elab = runElabNewGoal (ty :>: elab)

|EReturn| is the @return@ of the monad. It does nothing and always succeeds.

> runElab _ (_ :>: EReturn x) = return (x, ElabSuccess)


|ELambda| creates a \(\lambda\)-parameter, if this is allowed by the
type we are elaborating to.

> runElab WorkCurrentGoal (ty :>: ELambda x f) = case lambdable (ev ty) of
>     Just (_, s, tyf) -> do
>         h <- lambdaParam x
>         runElab WorkCurrentGoal (tyf (h :$ B0) :>: f h)
>     Nothing -> throwError' $ err "runElab: type" ++ errTyTm (SET :>: ty)
>                                  ++ err "is not lambdable!"

|EGoal| retrieves the current goal and passes it to the elaboration task.

> runElab wrk (ty :>: EGoal f) = runElab wrk (ty :>: f ty)


|EWait| makes a |Waiting| hole and pass it along to the next elaboration task.

> runElab wrk (ty :>: EWait s tyWait f) = do
>     tt <- make (s :<: tyWait)
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
>     t <- getCurrentDefinitionLocal
>     return (t, ElabSuspended)


|EFake| extracts the reference of the current entry and presents it as
 a fake reference. \pierre{This is an artifact of our current
 implementation of labels, this should go away when we label
 high-level objects with high-level names}.

<     r <- getFakeRef 
<     inScope <- getInScope
<     runElab WorkCurrentGoal . (ty :>:) $ f (r, paramSpine inScope)

|EAnchor| extracts the name of the current entry.

< runElab WorkCurrentGoal (ty :>: EAnchor f) = do
<     name <- getCurrentName
<     runElab WorkCurrentGoal . (ty :>:) $ f (fst (last name))


|EResolve| provides a name-resolution service: given a relative name,
 it finds the term and potentially the scheme of the definition the
 name refers to. This is passed onto the next elaboration task.


> runElab wrk (ty :>: EResolve rn f) = do
>     (t, l, ms) <- resolveHere rn
>     es <- getInScope
>     let  tm   = t $$$. bwdList (take l (params es))
>          ms'  = (| (stripScheme l) ms |)
>     tt <- inferHere t
>     ty' <- inferSpHere (t :<: tt) (map A (take l (params es))) 
>     runElab wrk (ty :>: f (PAIR ty' tm , ms'))


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

> runElab wrk (ty :>: EAskDevLev f) = do
>     l <- getDevLev
>     runElab wrk (ty :>: f l)

> runElab _ (_ :>: e) = error $ show e

As mentioned above, some commands can only be used when elaboration is taking
place in the current goal. This is the purpose of |runElabNewGoal|: it creates
a dummy definition and hands back the elaboration task to |runElab|.

> runElabNewGoal :: (TY :>: Elab EXP) -> ProofState (EXP, ElabStatus)
> runElabNewGoal (ty :>: elab) = do
>     -- Make a dummy definition
>     x <- pickName "h" ""
>     make (x :<: ty)
>     -- Enter its development
>     goIn
>     (tm, status) <- runElab WorkCurrentGoal (ty :>: elab)
>     -- Leave the development, one way or the other
>     d <- case status of
>            ElabSuccess -> giveOutBelow tm
>            ElabSuspended -> do
>                 -- By leaving it unfinished
>                 d <- getCurrentDefinition
>                 goOut
>                 return d
>     es <- getInScope
>     return $ (def d $$$ paramSpine es, status) 
  

\subsection{Interpreting elaboration problems}

The |runElabProb| interprets the syntactic representation of an
elaboration problem. In other words, this function defines the
semantics of the |EProb| language.

> runElabProb :: WorkTarget ->  Loc -> (TY :>: EProb) -> 
>                               ProofState (EXP, ElabStatus)


|ElabDone tt| always succeed at returning the given term |tt|.

> runElabProb wrk loc (ty :>: ElabDone tt)  = 
>     return (tt, ElabSuccess)

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

> runElabProb wrk loc (ty :>: p@(WaitCan tm prob)) =
>   case ev tm of
>     c :- as -> runElabProb wrk loc (ty :>: prob)
>     _ -> suspendThis wrk ("can" :<: ty) p Waiting


The semantics of the |ElabHope| command is specifically given by the
|runElabHope| interpreter in
Section~\ref{subsec:Elaboration.RunElab.elabHope}.

> runElabProb wrk loc (ty :>: ElabHope)     = runElabHope wrk (ev ty)


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
>     suspendThis top (name prob :<: ty) prob Waiting
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

\item An element of type |ONE| is |ZERO|;

\item A proof of a proposition might be found or refined by the
propositional simplifier
(Section~\ref{sec:Tactics.PropositionSimplify}); and

\item The solution of a programming is often an induction hypothesis
that is sitting in our context

\end{itemize}

If these strategies do not match or fail to solve the problem, we just
create a hole.

> runElabHope :: WorkTarget -> VAL -> ProofState (EXP, ElabStatus)
> runElabHope wrk ONE             = return (ZERO, ElabSuccess)

> {-
> runElabHope wrk (PRF p)             = simplifyProof wrk p
> -}

> runElabHope wrk v@(LABEL ty l)  = seekLabel wrk l ty <|> lastHope wrk v
> runElabHope wrk ty              = lastHope wrk ty


\subsubsection{Hoping for labelled types}

If we are looking for a labelled type (e.g.\ to make a recursive call), we
search the hypotheses for a value with the same label.

> seekLabel :: WorkTarget -> EXP -> TY -> ProofState (EXP, ElabStatus)
> seekLabel wrk label ty = do
>     es <- getInScope
>     seekOn es
>     where

The traversal of the hypotheses is carried by |seekOn|. It searches
parameters and hands them to |seekIn|.

>       seekOn B0                                    = do
>           s <- prettyPS (ty :>: label)
>           proofTrace $ "Failed to resolve recursive call to "
>                            ++ renderHouseStyle s
>           (|)
>       seekOn (es' :< EParam ParamLam s t l)  =  
>           seekIn l es' B0 (P (l, s, t) :$ B0) (ev t) <|> seekOn es'
>       seekOn (es' :< _)                            =    seekOn es'

Then, |seekIn| tries to match the label we are looking for with an
hypothesis we have found. Recall that a label is a telescope
targetting a label, hence we try to peel off this telescope to match
the label. 

>       seekIn :: Int -> Entries -> Bwd (Int, String, TY) -> EXP -> 
>                 VAL -> ProofState (EXP, ElabStatus)

On our way to the label, we instantiate the hypotheses with fresh references.

>       seekIn lev es rs tm (PI s t) = 
>         let dlst = (lev, fortran "x" [ev t] undefined, s)
>         in  seekIn (lev + 1) es (rs :< dlst) (tm $$. (P dlst :$ B0)) 
>                                              (ev (t $$. (P dlst :$ B0)))

We might have to go inside branches (essentially finite $\Pi$-types).

<       seekIn rs tm (N (op :@ [e, p])) | op == branchesOp =
<           freshRef (fortran p :<: e) $ \ eRef -> do
<               e' <- bquoteHere e
<               p' <- bquoteHere p
<               seekIn (rs :< eRef) (switchOp :@ [e', NP eRef, p', N tm])
<                   (p $$ A (pval eRef))

We have reached a label! The question is then ``is this the one we are looking
for?'' First we call on the matcher (see section~\ref{subsec:Tactics.Matching})
to find values for the fresh references, then we generate a substitution from
these values and apply it to the call term.

>       seekIn lev es rs tm (LABEL u foundLabel) | equal lev (SET :>: (ty,u)) =
>         do
>           ss <- execStateT (matchValue lev B0 
>                     (u :>: (ev foundLabel, ev label))) (fmap (, Nothing) rs)
>           ss'  <- processSubst [] ss 
>           return ((ss', INil) :/ tm, ElabSuccess)

If, in our way to the label the peeling fails, then we must give up.

>       seekIn _ _ _ _ _ = (|)

>       boys :: Entries -> [EXP] -> [EXP]
>       boys B0 bs = bs
>       boys (es :< EParam _ s t l) bs = boys es (P (l, s, t) :$ B0 : bs)
>       boys (es :< _) bs = boys es bs


To generate a substitution, we quote the value given to each reference and
substitute out the preceding references. If a reference has no value, i.e. it
is unconstrained by the matching problem, we hope for a solution.
\adam{we could do some dependency analysis here to avoid cluttering the proof
state with hopes that we don't make use of.}

>       processSubst :: LEnv {Z} -> MatchSubst -> ProofState (LEnv {Z})
>       processSubst bs B0           = return bs
>       processSubst bs (rs :< ((l,_,_), Just t))  = do
>           ss  <- processSubst bs rs
>           return ((l, (ss, INil) :/ t) : ss)
>       processSubst bs (rs :< ((l,_,ty), Nothing))  = do
>           ss  <- processSubst bs rs
>           (tm, _)  <- runElabHope WorkElsewhere (ev ((ss, INil) :/ ty))
>           return ((l,tm) : ss)


\subsubsection{Simplifying proofs}
\label{subsubsec:Elaboration.RunElab.proofs}

\pierre{To be reviewed.}

If we are hoping for a proof of a proposition, we first try simplifying it using
the propositional simplification machinery.

< simplifyProof :: WorkTarget -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
< simplifyProof wrk p = do
<     pSimp <- runPropSimplify p
<     case pSimp of
<         Just (SimplyTrivial prf) -> do
<             return (prf :=>: evTm prf, ElabSuccess)
<         Just (SimplyAbsurd _) -> runElab wrk (PRF p :>:
<             ECry [err "simplifyProof: proposition is absurd:"
<                          ++ errTyVal (p :<: PROP)])
<         Just (Simply qs _ h) -> do
<             qrs <- traverse partProof qs
<             let prf = substitute qs qrs h
<             return (prf :=>: evTm prf, ElabSuccess)
<         Nothing -> subProof wrk (PRF p)
<   where
<     partProof :: (REF :<: INTM) -> ProofState INTM
<     partProof (ref :<: _) = do
<       ((tm :=>: _) , _) <- subProof WorkElsewhere (pty ref)
<       return tm

<     subProof :: WorkTarget -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
<     subProof wrk (PRF p) = flexiProof wrk p <|> lastHope wrk (PRF p)


After simplification has dealt with the easy stuff, it calls |flexiProof| to
solve any flex-rigid equations (by suspending a solution process on a subgoal
and returning the subgoal). 

< flexiProof :: WorkTarget -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)

< flexiProof wrk (EQBLUE (_S :>: s) (_T :>: t)) = 
<     flexiProofMatch           (_S :>: s) (_T :>: t)
<     <|> flexiProofLeft   wrk  (_S :>: s) (_T :>: t)
<     <|> flexiProofRight  wrk  (_S :>: s) (_T :>: t)
< flexiProof _ _ = (|)

If we are trying to prove an equation between the same fake reference applied to
two lists of parameters, we prove equality of the parameters and use reflexivity.
This case arises frequently when proving label equality to make recursive calls.
\question{Do we need this case, or are we better off using matching?}

< flexiProofMatch :: (TY :>: VAL) -> (TY :>: VAL)
<     -> ProofState (INTM :=>: VAL, ElabStatus)
< flexiProofMatch (_S :>: N s) (_T :>: N t)
<   | Just (ref, ps) <- pairSpines s t [] = do
<     let ty = pty ref
<     prfs <- proveBits ty ps B0
<     let  q  = NP refl $$ A ty $$ A (NP ref) $$ Out
<          r  = CON (smash q (trail prfs))
<     r' <- bquoteHere r
<     return (r' :=>: r, ElabSuccess)
<   where
<     pairSpines :: NEU -> NEU -> [(VAL, VAL)] -> Maybe (REF, [(VAL, VAL)])
<     pairSpines (P ref@(sn := _ :<: _)) (P (tn := _ :<: _)) ps
<       | sn == tn   = Just (ref, ps)
<       | otherwise  = Nothing
<     pairSpines (s :$ A as) (t :$ A at) ps = pairSpines s t ((as, at):ps)
<     pairSpines _ _ _ = Nothing 

<     proveBits :: TY -> [(VAL, VAL)] -> Bwd (VAL, VAL, VAL)
<         -> ProofState (Bwd (VAL, VAL, VAL))
<     proveBits ty [] prfs = return prfs
<     proveBits (PI s t) ((as, at):ps) prfs = do
<         (_ :=>: prf, _) <- simplifyProof WorkElsewhere (EQBLUE (s :>: as) (s :>: at)) 
<         proveBits (t $$ A as) ps (prfs :< (as, at, prf))

<     smash :: VAL -> [(VAL, VAL, VAL)] -> VAL
<     smash q [] = q
<     smash q ((as, at, prf):ps) = smash (q $$ A as $$ A at $$ A prf) ps

< flexiProofMatch _ _ = (|)

If one side of the equation is a hoping hole applied to the shared parameters of
our current location, we can solve it with the other side of the equation.
\question{How can we generalise this to cases where the hole is under a different
list of parameters?}

\question{Can we hope for a proof of equality and
insert a coercion rather than demanding definitional equality of the sets?
See Elab.pig for an example where this makes the elaboration process fragile,
because we end up trying to move definitions with processes attached.}

< flexiProofLeft :: WorkTarget -> (TY :>: VAL) -> (TY :>: VAL)
<     -> ProofState (INTM :=>: VAL, ElabStatus)
< flexiProofLeft wrk (_T :>: N t) (_S :>: s) = do
<     guard =<< withNSupply (equal (SET :>: (_S, _T)))

<     (q' :=>: q, _) <- simplifyProof False (EQBLUE (SET :>: _S) (SET :>: _T))

<     ref  <- stripShared t
<     s'   <- bquoteHere s
<     _S'  <- bquoteHere _S
<     t'   <- bquoteHere t
<     _T'  <- bquoteHere _T
<     let  p      = EQBLUE (_T   :>: N t   ) (_S   :>: s   )
<          p'     = EQBLUE (_T'  :>: N t'  ) (_S'  :>: s'  )

<          N (coe :@ [_S', _T', q', s']) :=>: Just (coe @@ [_S, _T, q, s])

<          eprob  = WaitSolve ref (s' :=>: Just s) ElabHope

<     suspendThis wrk ("eq" :<: PRF p' :=>: PRF p) eprob
< flexiProofLeft _ _ _ = (|)



< flexiProofRight :: WorkTarget -> (TY :>: VAL) -> (TY :>: VAL)
<     -> ProofState (INTM :=>: VAL, ElabStatus)
< flexiProofRight wrk (_S :>: s) (_T :>: N t) = do
<     guard =<< withNSupply (equal (SET :>: (_S, _T)))
<     ref  <- stripShared t
<     s'   <- bquoteHere s
<     _S'  <- bquoteHere _S
<     t'   <- bquoteHere t
<     _T'  <- bquoteHere _T
<     let  p      = EQBLUE (_S   :>: s   ) (_T   :>: N t   )
<          p'     = EQBLUE (_S'  :>: s'  ) (_T'  :>: N t'  )
<          eprob  = WaitSolve ref (s' :=>: Just s) ElabHope
<     suspendThis wrk ("eq" :<: PRF p' :=>: PRF p) eprob
< flexiProofRight _ _ _ = (|)


If all else fails, we can hope for anything we like by leaving a hoping
subgoal, either using the current one (if we are working on it) or creating a
new subgoal. Ideally we should cry rather than hoping for something
patently absurd: at the moment we reject some impossible hopes but do not
always spot them.

> lastHope :: WorkTarget -> VAL -> ProofState (EXP, ElabStatus)
> lastHope WorkCurrentGoal ty = do
>     putHoleKind Hoping
>     return . (, ElabSuspended) =<< getCurrentDefinitionLocal
> lastHope WorkElsewhere ty = do
>     return . (, ElabSuccess) =<< makeKinded Nothing Hoping ("hope" :<: exp ty)


\subsection{Suspending computation}
\label{subsec:Elaboration.RunElab.suspending}

\pierre{To be reviewed.}


The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration problem to its tip.
When the scheduler hits the goal, the elaboration problem will restart if it
is unstable.

> suspend :: (String :<: EXP) -> EProb -> HKind -> ProofState EXP
> suspend (x :<: tt) prob hk = do
>     -- Make a hole
>     r <- make (x :<: tt)
>     goIn
>     -- Store the suspended problem
>     putDevTip (Suspended tt prob hk)
>     -- Mark the Suspension state
>     goOutBelow
>     let ss = if isUnstable prob then SuspendUnstable else SuspendStable
>     putDevSuspendState ss
>     -- Mark for Scheduler action \pierre{right?}
>     suspendHierarchy ss
>     return r

The |suspendMe| command attaches a suspended elaboration problem to
the current location. \pierre{We expect the tip to be in an |Unknown|
state. That's an invariant.}

> suspendMe :: EProb -> ProofState EXP
> suspendMe prob = do
>     -- Store the suspended problem in the Tip
>     Unknown tt hk <- getDevTip
>     putDevTip (Suspended tt prob hk)
>     -- Mark for Scheduler action \pierre{right?}
>     let ss = if isUnstable prob then SuspendUnstable else SuspendStable
>     suspendHierarchy ss
>     getCurrentDefinitionLocal


The |suspendThis| command attaches the problem to the current goal if
we are working on it, and creates a new subgoal otherwise.

> suspendThis :: WorkTarget ->  (String :<: EXP) -> EProb -> HKind -> 
>                               ProofState (EXP, ElabStatus)
> suspendThis WorkCurrentGoal _ ep hk = 
>     return . (, ElabSuspended) =<< suspendMe ep
> suspendThis WorkElsewhere  stt  ep hk = 
>     return . (, ElabSuccess)   =<< suspend stt ep hk

