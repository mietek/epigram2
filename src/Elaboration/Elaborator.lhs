\section{Invoking the Elaborator}
\label{sec:Elaborator.Elaborator}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.Elaborator where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Traversable
> import Data.Foldable

> import Evidences.Tm
> import Evidences.TypeChecker
> import Evidences.ErrorHandling

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Scope
> import ProofState.Edition.Navigation

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
> import Kit.NatFinVec
> import Kit.MissingLibrary

> import Debug.Trace

%endif


\subsection{Elaborating terms}

The |elaborate| command elaborates a term in display syntax, given its
type, to produce an elaborated term and its value representation. It
behaves similarly to |check| from
subsection~\ref{subsec:Evidences.TypeChecker.type-checking}, except that it
operates in the |Elab| monad, so it can create subgoals and
$\lambda$-lift terms.

> elaborate :: Loc -> (TY :>: DInTmRN) -> ProofState EXP
> elaborate loc (ty :>: tm) = runElab WorkElsewhere (ty :>: makeElab loc tm)
>     >>= return . fst

> elaborate' = elaborate (Loc 0)


> elaborateHere :: Loc -> DInTmRN -> ProofState (EXP, ElabStatus)
> elaborateHere loc tm = do
>     ty <- getHoleGoal
>     runElab WorkCurrentGoal (ty :>: makeElab loc tm)

> elaborateHere' = elaborateHere (Loc 0)


> elabInfer :: Loc -> DExTmRN -> ProofState (EXP :<: TY)
> elabInfer loc tm = do
>     (tt, _) <- runElab WorkElsewhere (sigSet :>: makeElabInfer loc tm)
>     return $ extractNeutral tt

> elabInfer' = elabInfer (Loc 0)


Sometimes (for example, if we are about to apply elimination with a motive) we
really want elaboration to proceed as much as possible. The |elabInferFully| command
creates a definition for the argument, elaborates it and runs the scheduler.

> elabInferFully :: DExTmRN -> ProofState (EXP :<: TY)
> elabInferFully tm = do
>     make ("eif" :<: sigSet)
>     goIn
>     (tm, status) <- runElab WorkCurrentGoal (sigSet :>: makeElabInfer (Loc 0) tm)
>     when (status == ElabSuccess) (ignore (give tm))
>     startScheduler
>     tm <- getCurrentDefinitionLocal
>     goOut
>     return (tm $$ Tl :<: tm $$ Hd)


\subsection{Elaborating construction commands}


The |elabGive| command elaborates the given display term in the appropriate type for
the current goal, and calls the |give| command on the resulting term. If its argument
is a nameless question mark, it avoids creating a pointless subgoal by simply returning
a reference to the current goal (applied to the appropriate shared parameters).

> elabGive :: DInTmRN -> ProofState EXP
> elabGive tm = elabGive' tm <* startScheduler <* goOut

> elabGiveNext :: DInTmRN -> ProofState EXP 
> elabGiveNext tm = elabGive' tm <* startScheduler <* (nextGoal <|> goOut)

> elabGive' :: DInTmRN -> ProofState EXP 
> elabGive' tm = do
>     tip <- getDevTip
>     case (tip, tm) of         
>         (Unknown _ _, DQ "")  -> return ()
>         (Unknown _ _, _)      -> do
>             (tm' , status) <- elaborateHere' tm
>             case status of
>               ElabSuccess -> give tm' >> return ()
>               ElabSuspended -> return () 
>         _  -> throwError' $ err "elabGive: only possible for incomplete goals."
>     getCurrentDefinitionLocal

The |elabMake| command elaborates the given display term in a module to
produce a type, then converts the module to a goal with that type. Thus any
subgoals produced by elaboration will be children of the resulting goal.

> elabMake :: (String :<: DInTmRN) -> ProofState EXP
> elabMake (s :<: ty) = do
>     makeModule s
>     goIn
>     ty' <- elaborate' (SET :>: ty)
>     tm <- moduleToGoal ty'
>     goOutBelow
>     return tm


The |elabPiParam| command elaborates the given display term to produce a type, and
creates a $\Pi$ with that type.

> elabPiParam :: (String :<: DInTmRN) -> ProofState (Tm {Head, s, Z})
> elabPiParam (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     piParamUnsafe (s :<: tt)

> elabLamParam :: (String :<: DInTmRN) -> ProofState (Tm {Head, s, Z})
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


> elabLet :: (String :<: DScheme) -> ProofState ()
> elabLet (x :<: sch) = do
>     makeModule x
>     goIn

First we need to elaborate the scheme so it contains evidence terms,
then convert the module into a goal with the scheme assigned.

>     make (x ++ "-type" :<: SET)
>     goIn
>     (sch', ty) <- elabLiftedScheme sch
>     trace "MadeTY" $ return ()
>     moduleToGoal ty
>     putCurrentScheme sch'
>     trace "putScheme" $ return () 


Now we add a definition with the same name as the function being defined,
to handle recursive calls. This has the same arguments as the function,
plus an implicit labelled type that provides evidence for the recursive call.

>     CDefinition d _ <- getCurrentEntry
> 
>     lev <- getDevLev
>     -- |pn :=>: _ <- getFakeCurrentEntry |
>     let fake :: Tm {Head, Exp, Z} ; fake = D d 
>     let schCall = makeCall fake 0 B0 sch'
>     us <- getParamsInScope
>     let schCallLocal = stripScheme lev schCall
>     let ty = schemeToType lev schCallLocal
>     make (x :<: ty)
>     goIn
>     putCurrentScheme schCall
>     let noms = schemeNames schCallLocal
>     traverse lambdaParam noms
>     us' <- getParamsInScope
>     let refs' :: Bwd (Elim EXP) ; refs' = bwdList $ map (\x -> A x) (init us')
>     let ll :: EXP ; ll = fake :$ refs'
>     giveOutBelow $ last us' $$ Call ll

For now we just call |elabProgram| to set up the remainder of the programming
problem. This could be implemented more cleanly, but it works.

>     makeModule "impl"
>     goIn
>     let schLocal = stripScheme (length us) sch'
>     (pis,ty') <- piSch fake schLocal (bwdList us)
>     moduleToGoal ty'
>     imp <- getCurrentDefinition 
>     goOut 
>     traverse lambdaParam (schemeNames schLocal)
>     as <- getParamsInScope
>     let refs'' :: Bwd (Elim EXP) ; refs'' = bwdList $ map (\x -> A x) as
>     let ll' :: EXP ; ll' = fake :$ refs''
>     give (def imp $$$ (refs'' :< Call ll'))
>     goIn 
>   where

>     makeCall :: Tm {Head, Exp, Z} -> Int -> Bwd EXP -> Scheme -> Scheme 
>     makeCall l n as (SchType ty) =
>         SchImplicitPi ("c" :<: LABEL ty (l :$ fmap A as))
>             (SchType ty)
>     makeCall l n as (SchImplicitPi (x :<: s) schT) =
>         SchImplicitPi (x :<: s) (makeCall l (n+1) (as :< P (n,x,s) :$ B0) schT)
>     makeCall l n as (SchExplicitPi (x :<: schS) schT) =
>         SchExplicitPi (x :<: schS) (makeCall l (n+1) (as :<
>           P (n,x,schemeToType n schS) :$ B0) schT )

>     piSch :: Tm {Head, Exp, Z} -> Scheme -> Bwd EXP -> ProofState ([Tm {Head, Exp, Z}],TY)
>     piSch h (SchImplicitPi xhazt schT) as = do
>       x <- assumeParam xhazt
>       (xs,ty) <- piSch h schT (as :< x :$ B0)
>       return (x : xs,ty)
>     piSch h (SchExplicitPi (x :<: schS) schT) as = do
>       lev <- getDevLev 
>       x <- assumeParam (x :<: schemeToType lev schS)
>       (xs,ty) <- piSch h schT (as :< x :$ B0)
>       return (x : xs,ty)
>     piSch h (SchType ty) as = return ([],LABEL ty (h :$ fmap A as))       

\subsection{Elaborating schemes}

> elabLiftedScheme :: DScheme -> ProofState (Scheme, TY)
> elabLiftedScheme sch = do
>     inScope    <- getInScope
>     (sch', d)  <- elabScheme sch
>     return (liftScheme inScope sch', Evidences.Tm.def d $$$ paramSpine inScope)

> liftScheme :: Entries -> Scheme -> Scheme
> liftScheme B0 sch                             = sch
> liftScheme (es :< EParam _ x s _) sch  =
>     liftScheme es (SchExplicitPi (x :<: SchType s) sch)
> liftScheme (es :< _) sch                      = liftScheme es sch


> elabScheme :: DScheme -> ProofState (Scheme, DEF)

> elabScheme (SchType ty) = do
>     ty'  <- elaborate' (SET :>: ty)
>     d    <- giveOutBelow ty'
>     return (SchType ty', d)

> elabScheme (SchExplicitPi (x :<: s) t) = do
>     make ("tau" :<: SET)
>     goIn
>     (s', sd) <- elabScheme s
>     es <- getInScope
>     piParam (x :<: Evidences.Tm.def sd $$$ paramSpine es)
>     (t', td) <- elabScheme t
>     return (SchExplicitPi (x :<: s') t', td)

> elabScheme (SchImplicitPi (x :<: s) t) = do
>     sty <- elaborate' (SET :>: s)
>     piParam (x :<: sty)
>     (t', td) <- elabScheme t
>     return (SchImplicitPi (x :<: sty) t', td)
