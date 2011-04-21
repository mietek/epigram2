\section{Making Parameters}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Parameter where

> import Kit.MissingLibrary
> import Kit.NatFinVec
> import Kit.BwdFwd

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.ProofKit

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.ErrorHandling

%endif



\subsection{|\|-abstraction}


When working at solving a goal, we might be able to introduce an
hypothesis. For instance, if the goal type is \(\Nat \To \Nat \To
\Nat\), we can introduce two hypotheses \(\V{x}\) and
\(\V{y}\). Further, the type of the goal governs the kind of the
parameter (a lambda, or a forall) and its type. This automation is
implemented by |lambdaParam| that lets you introduce a parameter above
the cursor while working on a goal.

> lambdaParam :: String -> ProofState (Tm {Head, s, Z})
> lambdaParam x = do
>     tip <- getDevTip
>     case tip of
>       Unknown ty ->
>         case lambdable (ev ty) of
>           Just (paramKind, s, t) -> do
>               -- Insert the parameter above the cursor
>               l <- getDevLev
>               putEntryAbove $ EParam paramKind x s l
>               putDevLev (succ l)
>               -- Update the Tip
>               let tipTy = t $ P (l, x, s) :$ B0
>               putDevTip $ Unknown tipTy
>               -- Return the reference to the parameter
>               return $ P (l, x, s)
>           _  -> throwError' $ err "lambdaParam: goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaParam: only possible for incomplete goals."


\subsection{Assumptions}

With |lambdaParam|, we can introduce parameters under a proof
goal. However, when working under a module, we would like to be able
to introduce hypothesis of some type. This corresponds to some kind of
``Assume'' mechanism, where we assume the existence of an object of
the provided type under the given module.

> assumeParam :: (String :<: TY) -> ProofState (Tm {Head, s, Z})
> assumeParam (x :<: ty)  = do
>     tip <- getDevTip
>     case tip of
>       Module -> do
>         l <- getDevLev
>         -- Simply make the reference
>         putEntryAbove $ EParam ParamLam x ty l
>         putDevLev (succ l)
>         return $ P (l, x, ty) 
>       _    -> throwError' $ err "assumeParam: only possible for modules."

\subsection{|Pi|-abstraction}

When working at defining a type (an object in |Set|), we can freely
introduce |Pi|-abstractions. This is precisely what |piParam| let us
do.

> piParam :: (String :<: EXP) -> ProofState (Tm {Head, s, Z})
> piParam (s :<: ty) = do
>   chkPS $ SET :>: ty
>   piParamUnsafe $ s :<: (ENil // ty)

The variant |piParamUnsafe| will not check that the proposed type is
indeed a type, so it requires further attention.

> piParamUnsafe :: (String :<: TY) -> ProofState (Tm {Head, s, Z})
> piParamUnsafe (s :<: ty) = do
>     tip <- getDevTip
>     case tip of
>         Unknown SET -> do
>           -- Working on a goal of type |Set|
>           l <- getDevLev
>           -- Simply introduce the parameter
>           putEntryAbove $ EParam ParamPi s ty l
>           putDevLev (succ l)
>           return $ P (l, s, ty)
>         Unknown _  -> throwError' $ err "piParam: goal is not of type SET."
>         _          -> throwError' $ err "piParam: only possible for incomplete goals."

