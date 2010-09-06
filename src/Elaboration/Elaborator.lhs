\section{Invoking the Elaborator}
\label{sec:Elaborator.Elaborator}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.Elaborator where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Traversable

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Eval
> import Evidences.TypeChecker
> import Evidences.Operators

> import Features.Features ()

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Scope
> import ProofState.Edition.Navigation
> import ProofState.Edition.FakeRef

> import ProofState.Interface.Search
> import ProofState.Interface.Module
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Lifting
> import ProofState.Interface.Parameter
> import ProofState.Interface.Definition
> import ProofState.Interface.Solving 

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme

> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.RunElab
> import Elaboration.Scheduler

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


\subsection{Elaborating terms}

The |elaborate| command elaborates a term in display syntax, given its
type, to produce an elaborated term and its value representation. It
behaves similarly to |check| from
subsection~\ref{subsec:Evidences.TypeChecker.type-checking}, except that it
operates in the |Elab| monad, so it can create subgoals and
$\lambda$-lift terms.

> elaborate :: Loc -> (TY :>: DInTmRN) -> ProofState (INTM :=>: VAL)
> elaborate loc (ty :>: tm) = runElab WorkElsewhere (ty :>: makeElab loc tm)
>     >>= return . fst

> elaborate' = elaborate (Loc 0)


> elaborateHere :: Loc -> DInTmRN -> ProofState (INTM :=>: VAL, ElabStatus)
> elaborateHere loc tm = do
>     _ :=>: ty <- getHoleGoal
>     runElab WorkCurrentGoal (ty :>: makeElab loc tm)

> elaborateHere' = elaborateHere (Loc 0)


> elabInfer :: Loc -> DExTmRN -> ProofState (INTM :=>: VAL :<: TY)
> elabInfer loc tm = do
>     (tt, _) <- runElab WorkElsewhere (sigSetVAL :>: makeElabInfer loc tm)
>     let (tt' :<: _ :=>: ty) = extractNeutral tt
>     return (tt' :<: ty)

> elabInfer' = elabInfer (Loc 0)


Sometimes (for example, if we are about to apply elimination with a motive) we
really want elaboration to proceed as much as possible. The |elabInferFully| command
creates a definition for the argument, elaborates it and runs the scheduler.

> elabInferFully :: DExTmRN -> ProofState (EXTM :=>: VAL :<: TY)
> elabInferFully tm = do
>     make ("eif" :<: sigSetTM)
>     goIn
>     (tm :=>: _, status) <- runElab WorkCurrentGoal (sigSetVAL :>: makeElabInfer (Loc 0) tm)
>     when (status == ElabSuccess) (ignore (give tm))
>     startScheduler
>     (tm :=>: v) <- getCurrentDefinition
>     goOut
>     return (tm :$ Snd :=>: v $$ Snd :<: v $$ Fst)


\subsection{Elaborating construction commands}


The |elabGive| command elaborates the given display term in the appropriate type for
the current goal, and calls the |give| command on the resulting term. If its argument
is a nameless question mark, it avoids creating a pointless subgoal by simply returning
a reference to the current goal (applied to the appropriate shared parameters).

> elabGive :: DInTmRN -> ProofState (EXTM :=>: VAL)
> elabGive tm = elabGive' tm <* startScheduler <* goOut

> elabGiveNext :: DInTmRN -> ProofState (EXTM :=>: VAL)
> elabGiveNext tm = elabGive' tm <* startScheduler <* (nextGoal <|> goOut)

> elabGive' :: DInTmRN -> ProofState (EXTM :=>: VAL)
> elabGive' tm = do
>     tip <- getDevTip
>     case (tip, tm) of         
>         (Unknown _, DQ "")  -> getDefn
>         (Unknown _, _)      -> do
>             (tm' :=>: _, status) <- elaborateHere' tm
>             case status of
>               ElabSuccess -> give tm'
>               ElabSuspended -> getDefn
>         _  -> throwError' $ err "elabGive: only possible for incomplete goals."
>   where
>     getDefn :: ProofState (EXTM :=>: VAL)
>     getDefn = do
>         CDefinition _ ref _ _ _ <- getCurrentEntry
>         aus <- getGlobalScope
>         return (applySpine ref aus)


The |elabMake| command elaborates the given display term in a module to
produce a type, then converts the module to a goal with that type. Thus any
subgoals produced by elaboration will be children of the resulting goal.

> elabMake :: (String :<: DInTmRN) -> ProofState (EXTM :=>: VAL)
> elabMake (s :<: ty) = do
>     makeModule s
>     goIn
>     ty' :=>: _ <- elaborate' (SET :>: ty)
>     tm <- moduleToGoal ty'
>     goOutBelow
>     return tm


The |elabPiParam| command elaborates the given display term to produce a type, and
creates a $\Pi$ with that type.

> elabPiParam :: (String :<: DInTmRN) -> ProofState REF
> elabPiParam (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     piParamUnsafe (s :<: tt)

> elabLamParam :: (String :<: DInTmRN) -> ProofState REF
> elabLamParam (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     assumeParam (s :<: tt)


\subsection{Elaborating programming problems}
\label{subsec:Elaborator.Elaborator.elab-prog-problem}

The |elabLet| command sets up a programming problem, given a name and
scheme. The command |let plus (m : Nat)(n : Nat) : Nat| should result
in the following proof state:

\begin{verbatim}
plus
    [ plus-type
        [ tau := Nat : Set ;
          (m : Nat) ->
          tau := Nat : Set ;
          (n : Nat) ->
        ] Nat : Set ;
      plus
        [ \ m : Nat ->
          \ n : Nat ->
          \ c : < plus^1 m n : Nat > ->
        ] c call : Nat ;
      plus-impl
        [ \ m : Nat ->
          \ n : Nat ->
        ] ? : < plus^1 m n : Nat > ;
      \ m : Nat ->
      \ n : Nat ->
    ] plus-impl m n call : Nat ;
\end{verbatim}

> elabLet :: (String :<: Scheme DInTmRN) -> ProofState (EXTM :=>: VAL)
> elabLet (x :<: sch) = do
>     makeModule x
>     goIn

First we need to elaborate the scheme so it contains evidence terms,
then convert the module into a goal with the scheme assigned.

>     make (x ++ "-type" :<: SET)
>     goIn
>     (sch', ty :=>: _) <- elabLiftedScheme sch
>     moduleToGoal (N ty)     
>     putCurrentScheme sch'

Now we add a definition with the same name as the function being defined,
to handle recursive calls. This has the same arguments as the function,
plus an implicit labelled type that provides evidence for the recursive call.

>     CDefinition _ (mnom := HOLE _ :<: ty) _ _ _ <- getCurrentEntry
>     pn :=>: _ <- getFakeCurrentEntry 
>     let schCall = makeCall (P $ mnom := FAKE :<: ty) 0 sch'
>     us <- getParamsInScope
>     let schCallLocal = applyScheme schCall us
>     make (x :<: schemeToInTm schCallLocal)
>     goIn
>     putCurrentScheme schCall
>     refs <- traverse lambdaParam (schemeNames schCallLocal)
>     giveOutBelow (N (P (last refs) :$ Call (N (pn $## map NP (init refs)))))

For now we just call |elabProgram| to set up the remainder of the programming
problem. This could be implemented more cleanly, but it works.

>     elabProgram (init $ schemeNames schCallLocal)
>   where

Sorry for the horrible de Bruijn index mangling.
\question{Perhaps we should use something
like |TEL| to represent schemes as telescopes of values?}

>     makeCall :: EXTM -> Int -> Scheme INTM -> Scheme INTM
>     makeCall l n (SchType ty) =
>         SchImplicitPi ("c" :<: LABEL (N (l $## fmap NV [n-1,n-2..0])) ty)
>             (SchType (inc 0 %% ty))
>     makeCall l n (SchImplicitPi (x :<: s) schT) =
>         SchImplicitPi (x :<: s) (makeCall l (n+1) schT)
>     makeCall l n (SchExplicitPi (x :<: schS) schT) =
>         SchExplicitPi (x :<: schS) (makeCall l (n+1) schT)


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
>     n   <- getCurrentName
>     pn  <- getFakeCurrentEntry 
>     (gUnlifted :=>: _) <- getHoleGoal
>     newty <- withNSupply $ pity (mkTel (unN $ valueOf pn) (evTm gUnlifted) [] args)
>     newty'       <- bquoteHere newty
>     impl :=>: _  <- make (magicImplName :<: newty') 
>     argrefs      <- traverse lambdaParam args
>     let  fcall  = termOf pn $## (map NP argrefs) 
>          call   = impl $## (map NP argrefs) :$ Call (N fcall)
>     r <- give (N call)
>     goIn
>     return r
>   where
>     mkTel :: NEU -> TY -> [VAL] -> [String] -> TEL TY
>     mkTel n (PI s t) args (x:xs)
>         = (x :<: s) :-: (\val -> mkTel n (t $$ A val) (val:args) xs)
>     mkTel n r args _ = Target (LABEL (mkL n (reverse args)) r)
>         
>     mkL :: NEU -> [VAL] -> VAL
>     mkL n [] = N n
>     mkL n (x:xs) = mkL (n :$ (A x)) xs

>     unN :: VAL -> NEU
>     unN (N n) = n


\subsection{Elaborating schemes}

> elabLiftedScheme :: Scheme DInTmRN -> ProofState (Scheme INTM, EXTM :=>: VAL)
> elabLiftedScheme sch = do
>     inScope <- getInScope
>     (sch', tt) <- elabScheme inScope sch
>     return (liftScheme inScope sch', tt)

> liftScheme :: Entries -> Scheme INTM -> Scheme INTM
> liftScheme B0 sch                             = sch
> liftScheme (es :< EPARAM _ (x, _) _ s _) sch  =
>     liftScheme es (SchExplicitPi (x :<: SchType (es -| s)) sch)
> liftScheme (es :< _) sch                      = liftScheme es sch


> elabScheme :: Entries -> Scheme DInTmRN -> ProofState (Scheme INTM, EXTM :=>: VAL)

> elabScheme es (SchType ty) = do
>     ty' :=>: _ <- elaborate' (SET :>: ty)
>     tt <- giveOutBelow ty'
>     return (SchType (es -| ty'), tt)

> elabScheme es (SchExplicitPi (x :<: s) t) = do
>     make ("tau" :<: SET)
>     goIn
>     (s', ty :=>: _) <- elabScheme es s
>     piParam (x :<: N ty)
>     e <- getEntryAbove
>     (t', tt) <- elabScheme (es :< e) t
>     return (SchExplicitPi (x :<: s') t', tt)

> elabScheme es (SchImplicitPi (x :<: s) t) = do
>     ss <- elaborate' (SET :>: s)
>     piParam (x :<: termOf ss)
>     e <- getEntryAbove
>     (t', tt) <- elabScheme (es :< e) t
>     return (SchImplicitPi (x :<: (es -| termOf ss)) t', tt)
