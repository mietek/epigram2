\section{Making Parameters}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Parameter where

> import Kit.MissingLibrary

> import NameSupply.NameSupplier

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.ProofKit

> import Evidences.Tm
> import Evidences.Rules

%endif



The following piece of kit might profitably be shifted to somewhere more
general.

> lambdable :: TY -> Maybe (ParamKind, TY, VAL -> TY)
> lambdable (PI s t)         = Just (ParamLam, s, (t $$) . A)
> lambdable (PRF (ALL s p))  = Just (ParamAll, s, \v -> PRF (p $$ A v))
> lambdable _                = Nothing



When working at solving a goal, we might be able to introduce an
hypothesis. For instance, if the goal type is \(\Nat \To \Nat \To
\Nat\), we can introduce two hypotheses \(\V{x}\) and
\(\V{y}\). Further, the type of the goal governs the kind of the
parameter (a lambda, or a forall) and its type. This automation is
implemented by |lambdaParam| that lets you introduce a parameter above
the cursor while working on a goal.

> lambdaParam :: String -> ProofState REF
> lambdaParam x = do
>     tip <- getDevTip
>     case tip of
>       Unknown (pi :=>: ty) -> 
>         -- Working at solving a goal
>         case lambdable ty of
>         Just (paramKind, s, t) -> 
>             -- Where can rightfully introduce a lambda
>             freshRef (x :<: s) $ \ref -> do
>               sTm <- bquoteHere s
>               -- Insert the parameter above the cursor
>               putEntryAbove $ EPARAM ref (mkLastName ref) paramKind sTm
>               -- Update the Tip
>               let tipTy = t $ pval ref
>               tipTyTm <- bquoteHere tipTy
>               putDevTip (Unknown (tipTyTm :=>: tipTy))
>               -- Return the reference to the parameter
>               return ref
>         _  -> throwError' $ err "lambdaParam: goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaParam: only possible for incomplete goals."



With |lambdaParam|, we can introduce parameters under a proof
goal. However, when working under a module, we would like to be able
to introduce hypothesis of some type

 The |lambdaParamTyped|
variant allows a type to be specified, so it can be used with
modules. If used at an |Unknown| tip, it will check that the supplied
type matches the one at the tip.

> assumeParam :: (String :<: (INTM :=>: TY)) -> ProofState REF
> assumeParam (x :<: (tyTm :=>: ty))  = do
>     tip <- getDevTip
>     case tip of
>       Module -> 
>         -- Working under a module
>         freshRef (x :<: ty) $ \ref -> do
>           -- Simply make the reference
>           putEntryAbove $ EPARAM ref (mkLastName ref) ParamLam tyTm
>           return ref
>       _    -> throwError' $ err "assumeParam: only possible for modules."




The |piParam| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piParam :: (String :<: INTM) -> ProofState REF
> piParam (s :<: ty) = checkHere (SET :>: ty) >>= piParam' . (s :<:)

> piParam' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> piParam' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> freshRef (s :<: tv) (\ref -> do
>             putEntryAbove (EPARAM ref (mkLastName ref) ParamPi ty)
>             return ref
>           )
>         Unknown _  -> throwError' $ err "piParam: goal is not of type SET."
>         _          -> throwError' $ err "piParam: only possible for incomplete goals."
