\section{Implementing the |Elab| monad}
\label{sec:Elaborator.RunElab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.RunElab where

> import Control.Applicative
> import Control.Monad.Error
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

> import Tactics.PropositionSimplify

> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.Unification
> import Elaboration.Wire hiding (AtToplevel (..))

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

> runElab :: AtToplevel ->  (TY :>: Elab (INTM :=>: VAL)) -> 
>                           ProofState (INTM :=>: VAL, ElabStatus)

Intuitively, the |Elab| code describes a series of ProofState
operations executed within the development of a definition of the
given type. \pierre{What is the semantics of the command? Why do we
give a type?} \pierre{Instead of passing the type around, couldn't we
get it from the |currentEntry| dynamically?}

However, if we are at the top-level of the ProofState, we are not
working under a development: therefore, we manually track our position
using the |AtToplevel| flag. \pierre{See bug \#51 concerning |AtTopLevel|}

> data AtToplevel = Toplevel | WithinDevelopment

When we are at the top-level, we artificially create a definition and
repeat the operation within the newly created development. The
commands that cannot be executed at the top-level are the
following:

> inDevelopmentOnly :: Elab x -> Bool
> inDevelopmentOnly (ELambda _ _)  =  True
> inDevelopmentOnly (ECry _)       =  True
> inDevelopmentOnly (EFake _)      =  True
> inDevelopmentOnly (EAnchor _)    =  True
> inDevelopmentOnly _              =  False

\pierre{What is the formal definition of "top-level"?} 
\pierre{Why Lambda and friends needs a special case?}


The execution of an elaboration either succeeds, meaning that a term
has been made \pierre{right?}, or ends in a suspended state, meaning that
further informations are awaited before being able to move on.

> data ElabStatus = ElabSuccess | ElabSuspended deriving Eq

Now, let us give the semantics of each command in turn. First of all,
we catch all commands that are \emph{incompatible} with the top-level
and redirect them to the specially crafted |runElabToplevel|.

> runElab Toplevel (ty :>: elab) | inDevelopmentOnly elab = runElabToplevel (ty :>: elab)

|EReturn| is the @return@ of the monad. It does nothing and always
 succeeds.

> runElab _ (_ :>: EReturn x) = return (x, ElabSuccess)

|ELambda| creates a \(\lambda\)-parameter, if this is allowed by the
type we are elaborating to.

> runElab WithinDevelopment (ty :>: ELambda x f) = do
>   case lambdable ty of
>     Just (_, s, tyf) -> do
>         ref <- lambdaParam x
>         runElab WithinDevelopment (tyf (NP ref) :>: f ref)
>     Nothing -> throwError' $ err "runElab: type" ++ errTyVal (ty :<: SET)
>                                  ++ err "is not lambdable!"

|EGoal| retrieves the current goal and use it to form a subsequent
 elaboration task.

> runElab top (ty :>: EGoal f) = runElab top (ty :>: f ty)

|EWait| makes a |Waiting| hole and pass it along to the next
 elaboration task.

> runElab top (ty :>: EWait s tyWait f) = do
>     tyWait' <- bquoteHere tyWait
>     tt <- make (s :<: tyWait')
>     runElab top (ty :>: f tt)

|EElab| contains a syntactic representation of an elaboration
task. This representation is interpreted and executed by
|runElabProb|.

> runElab top (ty :>: EElab l p)  = runElabProb top l (ty :>: p)

|ECompute| allows us to combine elaboration tasks: we run a first task
 and pass its result to the next elaboration task.

> runElab top (ty :>: ECompute (tyComp :>: elab) f) = do
>     -- \question{how do we know we are at toplevel?}
>     (e , _) <- runElab Toplevel (tyComp :>: elab) 
>     runElab top (ty :>: f e)

|ECry| is used to report an error. It updates the current entry into a
 crying state.

> runElab WithinDevelopment (ty :>: ECry e) = do
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

> runElab WithinDevelopment (ty :>: EFake f) = do
>     r <- getFakeRef 
>     inScope <- getInScope
>     runElab WithinDevelopment . (ty :>:) $ f (r, paramSpine inScope)

|EAnchor| extracts the name of the current entry.

> runElab WithinDevelopment (ty :>: EAnchor f) = do
>     name <- getCurrentName
>     runElab WithinDevelopment . (ty :>:) $ f (fst (last name))


|EResolve| provides a name-resolution service: given a relative name,
 it finds the term and potentially the scheme of the definition the
 name refers to. This is passed onto the next elaboration task.

> runElab top (ty :>: EResolve rn f) = do
>     (ref, as, ms) <- resolveHere rn
>     let  tm   = P ref $:$ toSpine as
>          ms'  = (| (flip applyScheme as) ms |)
>     (tmv :<: tyv) <- inferHere tm
>     tyv'  <- bquoteHere tyv
>     runElab top (ty :>: f (PAIR tyv' (N tm) :=>: PAIR tyv tmv, ms'))
>   

|EAskNSupply| gives access to the name supply to the next elaboration
 task.

\begin{danger}[Read-only name supply]

As often, we are giving here a read-only access to the name
supply. Therefore, we must be careful not to let some generated names
dangling into some definitions, or clashes could happen.

\end{danger}

> runElab top (ty :>: EAskNSupply f) = do
>     nsupply <- askNSupply
>     runElab top (ty :>: f nsupply)


As mentioned above, when we are at the top-level, some commands
requires an artificial development to be created before they are
executed. This is the purpose of |runElabToplevel|: it creates a dummy
definition and hands back the elaboration task to |runElab|.

> runElabToplevel :: (TY :>: Elab (INTM :=>: VAL)) -> ProofState (INTM :=>: VAL, ElabStatus)
> runElabToplevel (ty :>: elab) = do
>     -- Make a dummy definition
>     ty' <- bquoteHere ty
>     x <- pickName "h" ""
>     make (x :<: ty')
>     -- Enter its development
>     goIn
>     (tm :=>: tmv, status) <- runElab WithinDevelopment (ty :>: elab)
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

> runElabProb :: AtToplevel ->  Loc -> (TY :>: EProb) -> 
>                               ProofState (INTM :=>: VAL, ElabStatus)

|ElabDone tt| always succeed at returning the given term |tt|.

> runElabProb top loc (ty :>: ElabDone tt)  = 
>     return (maybeEval tt, ElabSuccess)

|ElabProb tm| asks for the elaboration of the display term |tm| (for
 pushed-in terms).

> runElabProb top loc (ty :>: ElabProb tm)  =
>     runElab top (ty :>: makeElab loc tm)

|ElabInferProb tm| asks for the elaboration and type inference of the
 display term |tm| (for pull-out terms).

> runElabProb top loc (ty :>: ElabInferProb tm) =
>     runElab top (ty :>: makeElabInfer loc tm)

|WaitCan tm prob| conditiones the interpretation of the elaboration
 problem |prob| to the fact that |tm| is indeed a canonical
 objects. Otherwise, the problem is indefinitely suspended.

\pierre{This fall-through pattern-match reminds me of Duff's devices.}

> runElabProb top loc (ty :>: WaitCan (_ :=>: Just (C _)) prob) =
>     runElabProb top loc (ty :>: prob)
> runElabProb top loc (ty :>: WaitCan (tm :=>: Nothing) prob) =
>     runElabProb top loc (ty :>: WaitCan (tm :=>: Just (evTm tm)) prob)

The semantics of the |ElabHope| command is specifically given by the
|runElabHope| interpreter in
Section~\ref{subsec:Elaboration.RunElab.elabHope}.

> runElabProb top loc (ty :>: ElabHope)     = runElabHope top ty

Any case that has not matched yet ends in a suspended state: we cannot
make progress on it right now. The suspension of an elaboration
problem is decribed in details in
Section~\label{subsec:Elaboration.RunElab.suspending}. Once in a
suspended state, an elaboration problem might receive some care from
the Scheduler (Section~\ref{sec:Elaboration.Scheduler}), which might
be able to make some progress.

The following problems are suspended, for different reasons:
\begin{itemize}

\item A |WaitCan| command offering an object that is \emph{not}
canonical;

\item A |WaitSolve| command, because we can make a term out of thin
air and we hope that the scheduler will be able to make some progress
for us; and

\item A |ElabSchedule| command, which purpose is to suspend the
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
Propositional simplifier
(Section~\ref{sec:Tactics.PropositionSimplify}); and

\item The solution of a programming is often an induction hypothesis
that is sitting in our context

\end{itemize}

If these strategies do not match or fail to solve the problem, we just
create a hole.

> runElabHope :: AtToplevel -> TY -> ProofState (INTM :=>: VAL, ElabStatus)
> runElabHope top UNIT                = return (VOID :=>: VOID, ElabSuccess)
> runElabHope top (PRF p)             = simplifyProof top p
> runElabHope top v@(LABEL (N l) ty)  = seekLabel top l ty <|> lastHope top v
> runElabHope top ty                  = lastHope top ty


\subsubsection{Hoping for labelled types}

If we are looking for a labelled type (e.g.\ to make a recursive call), we
search the hypotheses for a value with the same label.

> seekLabel :: AtToplevel -> NEU -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
> seekLabel top label ty = do
>     es <- getInScope
>     seekOn es
>     where

The traversal of the hypotheses is carried by |seekOn|. It searches
parameters and hands them to |seekIn|.

>       seekOn B0                                    =    (|)
>       seekOn (es' :< EPARAM param _ ParamLam _ _)  =    seekIn (NP param) (pty param)
>                                                    <|>  seekOn es'
>       seekOn (es' :< _)                            =    seekOn es'

Then, |seekIn| tries to match the label we are looking for with an
hypothesis we have found. Recall that a label is a telescope
targetting a label, hence we try to peal off this telescope to match
the label. 

>       seekIn :: VAL -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)

On our way to the label, we instantiate this bit and move forward.

\pierre{What do we do with the resulting hoping problems later on? Are
they solved at some point?}

\pierre{Note that making |s| at |Toplevel| means that |lastHope| will
deal with it as an |ElabSuccess|. This might be an important
invariant?}

>       seekIn tm (PI s t) = do
>        -- \question{How do we know we are |Toplevel| here?}
>        (st :=>: sv, _) <- runElabHope Toplevel s 
>        seekIn (tm $$ A sv) (t $$ A sv)

We have reached a label! The question is then "is it the one we are looking
for?". 

>       seekIn tm (LABEL (N foundLabel) u) = do
>         -- Tries to match the labels
>         case matchLabels foundLabel label [] of
>          Just (ref, vvs) -> do
>           -- Success!
>           labelTm  <- bquoteHere label
>           tyTm     <- bquoteHere ty
>           tmTm     <- bquoteHere tm
>           let labelTmVal = LABEL (N labelTm) tyTm :=>: LABEL (N label) ty
>           -- Match the telescopes
>           subst    <- matchParams (pty ref) vvs [] 
>           waitTm <- makeWait subst tmTm
>           suspendThis top ("label" :<: labelTmVal) waitTm
>          _ -> 
>           -- Failure.
>           (|)


If, in our way to the label, the pealing fails, we must give up.

>       seekIn tm ty = (|)




\pierre{Hopefully, this code will become less hairy when we have
proper high-level names.}

Because labels are stored lambda-lifted, we have to peal off their
parameters. Besides, we must accumulate them as we later need to check
that they are indeed equivalent (|matchParams|).

> matchLabels :: NEU -> NEU -> [(VAL, VAL)] -> Maybe (REF, [(VAL, VAL)])
> matchLabels (P ref@(sn := FAKE :<: _)) (P (tn := FAKE :<: _)) ps
>     | sn == tn   = Just (ref, ps)
>     | otherwise  = Nothing
> matchLabels (s :$ A as) (t :$ A at) ps = matchLabels s t ((as, at):ps)
> matchLabels _ _ _ = Nothing 

\pierre{This is fairly disgusting as well. Could we find a
presentation where |matchParams| and |makeWait| are fused? Instead of
a first pass that generates a weirdly reversed list and a second pass
that does something semantically sensible.}

When we know that we are talking about the same label, we are facing a
unification problem: the arguments of the label we are looking for
have to be matched to the arguments of the label we have found. The
latter has been elaborated as waiting holes in the ProofState:
unification will resolve them. \pierre{Is it \emph{guaranteed} to
solve them all? Or some could refuse to unify?}. \pierre{This bit
needs a better story.}

> matchParams :: TY -> [(VAL, VAL)] -> [(REF, VAL)] -> ProofState [(REF, VAL)]
> matchParams ty        []               subst = return subst
> matchParams (PI s t)  ((as, at) : ps)  subst = do
>     subst' <- valueMatch (s :>: (as, at))
>     matchParams (t $$ A as) ps (subst ++ subst')
> 
> makeWait :: [(REF, VAL)] -> INTM -> ProofState EProb
> makeWait []              g  = 
>     return $ ElabDone (g :=>: Nothing)
> makeWait ((r, v) : rvs)  g  = do
>     v' <- bquoteHere v
>     ep <- makeWait rvs g
>     return $ WaitSolve r (v' :=>: Just v) ep


\subsubsection{Simplifying proofs}
\label{subsubsec:Elaboration.RunElab.proofs}

\pierre{To be reviewed.}

If we are hoping for a proof of a proposition, we first try simplifying it using
the propositional simplification machinery.

> simplifyProof :: AtToplevel -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
> simplifyProof top p = do
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Just (SimplyTrivial prf) -> do
>             return (prf :=>: evTm prf, ElabSuccess)
>         Just (SimplyAbsurd _) -> runElab top (PRF p :>:
>             ECry [err "simplifyProof: proposition is absurd:"
>                          ++ errTyVal (p :<: PROP)])
>         Just (Simply qs _ h) -> do
>             qrs <- traverse partProof qs
>             let prf = substitute qs qrs h
>             return (prf :=>: evTm prf, ElabSuccess)
>         Nothing -> subProof top (PRF p)
>   where
>     partProof :: (REF :<: INTM) -> ProofState INTM
>     partProof (ref :<: _) = do
>       -- \question{how do we know we are at toplevel here?}
>       ((tm :=>: _) , _) <- subProof Toplevel (pty ref)
>       return tm

>     subProof :: AtToplevel -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)
>     subProof top (PRF p) = flexiProof top p <|> lastHope top (PRF p)


After simplification has dealt with the easy stuff, it calls |flexiProof| to
solve any flex-rigid equations (by suspending a solution process on a subgoal
and returning the subgoal). 

> flexiProof :: AtToplevel -> VAL -> ProofState (INTM :=>: VAL, ElabStatus)

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
>     -> ProofState (INTM :=>: VAL, ElabStatus)
> flexiProofMatch (_S :>: N s) (_T :>: N t)
>   | Just (ref, ps) <- matchLabels s t [] = do
>     let ty = pty ref
>     prfs <- proveBits ty ps B0
>     let  q  = NP refl $$ A ty $$ A (NP ref) $$ Out
>          r  = CON (smash q (trail prfs))
>     r' <- bquoteHere r
>     return (r' :=>: r, ElabSuccess)
>   where
>     proveBits :: TY -> [(VAL, VAL)] -> Bwd (VAL, VAL, VAL)
>         -> ProofState (Bwd (VAL, VAL, VAL))
>     proveBits ty [] prfs = return prfs
>     proveBits (PI s t) ((as, at):ps) prfs = do
>         -- \question{how do we know we are at toplevel here?}
>         (_ :=>: prf, _) <- simplifyProof Toplevel (EQBLUE (s :>: as) (s :>: at)) 
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

> flexiProofLeft :: AtToplevel -> (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, ElabStatus)
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

>          eprob  = WaitSolve ref (s' :=>: Just s) ElabHope

>     suspendThis top ("eq" :<: PRF p' :=>: PRF p) eprob
> flexiProofLeft _ _ _ = (|)



> flexiProofRight :: AtToplevel -> (TY :>: VAL) -> (TY :>: VAL)
>     -> ProofState (INTM :=>: VAL, ElabStatus)
> flexiProofRight top (_S :>: s) (_T :>: N t) = do
>     guard =<< withNSupply (equal (SET :>: (_S, _T)))
>     ref  <- stripShared t
>     s'   <- bquoteHere s
>     _S'  <- bquoteHere _S
>     t'   <- bquoteHere t
>     _T'  <- bquoteHere _T
>     let  p      = EQBLUE (_S   :>: s   ) (_T   :>: N t   )
>          p'     = EQBLUE (_S'  :>: s'  ) (_T'  :>: N t'  )
>          eprob  = WaitSolve ref (s' :=>: Just s) ElabHope
>     suspendThis top ("eq" :<: PRF p' :=>: PRF p) eprob
> flexiProofRight _ _ _ = (|)




If all else fails, we can hope for anything we like by creating a
subgoal, though ideally we should cry rather than hoping for something
patently absurd \pierre{Does that mean that the current code is not
doing the ideal thing?  Or what?}. \pierre{Todo: justify the different
behavior of |lastHope| depending on the top-level position.}

> lastHope :: AtToplevel -> TY -> ProofState (INTM :=>: VAL, ElabStatus)
> lastHope WithinDevelopment ty = do
>     putHoleKind Hoping
>     return . (, ElabSuspended) =<< neutralise =<< getCurrentDefinition
> lastHope Toplevel ty = do
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


The |suspendThis| command attaches the problem to the current hole if
we are not at top-level, and creates a new subgoal otherwise.

> suspendThis :: AtToplevel ->  (String :<: INTM :=>: TY) -> EProb -> 
>                               ProofState (INTM :=>: VAL, ElabStatus)
> suspendThis WithinDevelopment _ ep  = 
>     return . (, ElabSuspended)  =<< neutralise =<< suspendMe ep
> suspendThis Toplevel  stt  ep = 
>     return . (, ElabSuccess)   =<< neutralise =<< suspend stt ep
