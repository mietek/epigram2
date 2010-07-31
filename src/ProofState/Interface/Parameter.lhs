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


The |lambdaParam| command checks that the current goal is a $\Pi$-type, and if so,
appends a $\lambda$-abstraction with the appropriate type to the current development.

> lambdaBoy :: String -> ProofState REF
> lambdaBoy x = do
>     tip <- getDevTip
>     case tip of
>       Unknown (pi :=>: ty) -> case lambdable ty of
>         Just (k, s, t) -> freshRef (x :<: s) (\ref -> do
>             s' <- bquoteHere s
>             putEntryAbove (EPARAM ref (mkLastName ref) k s')
>             let tipTyv = t (pval ref)
>             tipTy <- bquoteHere tipTyv
>             putDevTip (Unknown (tipTy :=>: tipTyv))
>             return ref
>           )
>         _  -> throwError' $ err "lambdaBoy: goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaBoy: only possible for incomplete goals."

The |lambdaBoy'| variant allows a type to be specified, so it can
be used with modules. If used at an |Unknown| tip, it will check
that the supplied type matches the one at the tip.

> lambdaBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> lambdaBoy' (x :<: (ty :=>: tv))  = do
>     tip <- getDevTip
>     case tip of
>       Module -> freshRef (x :<: tv) (\ref -> do
>           putEntryAbove (EPARAM ref (mkLastName ref) ParamLam ty)
>           return ref
>         )
>       Unknown (pi :=>: gty) -> case lambdable gty of
>         Just (k, s, t) -> do
>           eq <- withNSupply (equal (SET :>: (tv, s)))
>           if eq
>             then freshRef (x :<: tv) (\ref -> do
>                 putEntryAbove (EPARAM ref (mkLastName ref) k ty)
>                 let tipTyv = t (pval ref)
>                 tipTy <- bquoteHere tipTyv
>                 putDevTip (Unknown (tipTy :=>: tipTyv))
>                 return ref
>               )
>             else throwError' $ err "lambdaBoy': given type does not match domain of goal."
>         _  -> throwError' $ err "lambdaBoy': goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaBoy': only possible for modules or incomplete goals."

The |piBoy| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piBoy :: (String :<: INTM) -> ProofState REF
> piBoy (s :<: ty) = checkHere (SET :>: ty) >>= piBoy' . (s :<:)

> piBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> piBoy' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> freshRef (s :<: tv) (\ref -> do
>             putEntryAbove (EPARAM ref (mkLastName ref) ParamPi ty)
>             return ref
>           )
>         Unknown _  -> throwError' $ err "piBoy: goal is not of type SET."
>         _          -> throwError' $ err "piBoy: only possible for incomplete goals."
