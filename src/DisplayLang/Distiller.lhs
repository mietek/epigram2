\section{Distillation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module DisplayLang.Distiller where

> import Data.Foldable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Developments
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Rules
> import Evidences.Tm
> import Evidences.Mangler


%endif


The |distill| command converts a typed INTM in the evidence language
to a term in the display language; that is, it reverses |elaborate|.
It performs christening at the same time. For this, it needs a list
of entries in scope, which it will extend when going under a binder.

> distill :: Entries -> (TY :>: INTM) -> ProofState (InDTmRN :=>: VAL)

> import <- DistillRules

> distill es (C ty :>: C c) = do
>     cc <- canTy (distill es) (ty :>: c)
>     return ((DC $ fmap termOf cc) :=>: evTm (C c))

> distill es (ty :>: l@(L sc)) = do
>     (k, s, f) <- lambdable ty `catchMaybe` ("distill: type " ++ show ty ++ " is not lambdable.")
>     let x = fortran l
>     tm' :=>: _ <- freshRef (x :<: s) (\ref ->
>         distill (es :< E ref (lastName ref) (Boy k)
>                  (error "distill: boy type undefined"))
>                 (f (pval ref) :>: underScope sc ref)
>       )
>     return $ DL (convScope sc x tm') :=>: (evTm $ L sc)
>   where
>     convScope :: Scope {TT} REF -> String -> InDTmRN -> DScope RelName
>     convScope (_ :. _)  x  tm = x ::. tm
>     convScope (K _)     _  tm = DK tm

> distill es (_ :>: N n) = do
>     (n' :<: _) <- distillInfer es n []
>     return (DN n' :=>: evTm n)

> distill _ (ty :>: tm) = error ("distill: can't cope with\n" ++ show ty ++ "\n:>:\n" ++ show tm)


The |distillInfer| command is the |EXTM| version of |distill|, which also yields
the type of the term. It keeps track of a list of entries in scope, but
also accumulates a spine so shared parameters can be removed.

> distillInfer :: Entries -> EXTM -> Spine {TT} REF -> ProofState (ExDTmRN :<: TY)

> import <- DistillInferRules

> distillInfer es tm@(P (name := _ :<: ty)) as       = do
>     me <- getMotherName
>     let (relName, argsToDrop) = baptise es me B0 name
>     (e', ty') <- processArgs (evTm tm :<: ty) as
>     return (DP relName $::$ (drop argsToDrop e') :<: ty')
>   where
>     processArgs :: (VAL :<: TY) -> Spine {TT} REF -> ProofState (DSpine RelName, TY)
>     processArgs (_ :<: ty) [] = return ([], ty)
>     processArgs (v :<: C ty) (a:as) = do
>         (e', ty') <- elimTy (distill es) (v :<: ty) a
>         (es, ty'') <- processArgs (v $$ (fmap valueOf e') :<: ty') as 
>         return (fmap termOf e' : es, ty'')

> distillInfer es (t :$ e) as    = distillInfer es t (e : as)

> distillInfer es (op :@ ts) as  = do
>     (ts', ty) <- opTy op (distill es) ts
>     return ((op ::@ fmap termOf ts') :<: ty) 

> distillInfer es (t :? ty) as   = do
>     ty'  :=>: vty  <- distill es (SET :>: ty)
>     t'   :=>: _    <- distill es (vty :>: t)
>     return ((DType ty' ::$ A t') :<: vty)

> distillInfer _ tm _ = error ("distillInfer: can't cope with " ++ show tm)