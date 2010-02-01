\section{Distillation}
\label{sec:distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module DisplayLang.Distiller where

> import Control.Monad.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Developments
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import NameSupply.NameSupplier

> import Evidences.Rules
> import Evidences.Tm
> import Evidences.Mangler


%endif


The |distill| command converts a typed INTM in the evidence language
to a term in the display language; that is, it reverses |elaborate|.
It performs christening at the same time. For this, it needs a list
of entries in scope, which it will extend when going under a binder.

> distill :: Entries -> (TY :>: INTM) -> ProofStateT INTM (InDTmRN :=>: VAL)

> import <- DistillRules

Just like in any other checker-evaluator, canonical terms can be distilled
using |canTy|.

> distill es (C ty :>: C c) = do
>     cc <- {- mliftError $ -} canTy (distill es) (ty :>: c)
>     return ((DC $ fmap termOf cc) :=>: evTm (C c))

To distill a $lambda$-abstraction, we speculate a fresh reference and distill
under the binder, then convert the scope appropriately.

> distill es (ty :>: l@(L sc)) = do
>     (k, s, f) <- lambdable ty `catchMaybe`  (err "distill: type " 
>                                             ++ errVal ty 
>                                             ++ err " is not lambdable.")
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

If we encounter a neutral term, we switch to |distillInfer|.

> distill es (_ :>: N n) = do
>     (n' :<: _) <- distillInfer es n []
>     return (DN n' :=>: evTm n)

If none of the cases match, we complain loudly.

> distill _ (ty :>: tm) = error ("distill: can't cope with\n" ++ show ty ++ "\n:>:\n" ++ show tm)


The |distillInfer| command is the |EXTM| version of |distill|, which also yields
the type of the term. It keeps track of a list of entries in scope, but
also accumulates a spine so shared parameters can be removed.

> distillInfer :: Entries -> EXTM -> Spine {TT} REF -> ProofStateT INTM (ExDTmRN :<: TY)

> import <- DistillInferRules

To distill a parameter with a spine of eliminators, we use |baptise| to determine
a name for the reference and the number of shared parameters, then process the
arguments and return the distilled application with the shared parameters dropped.

> distillInfer es tm@(P (name := _ :<: ty)) as       = do
>     me <- getMotherName
>     let (relName, argsToDrop) = baptise es me B0 name
>     (e', ty') <- processArgs es (evTm tm :<: ty) as
>     return ((DP relName $::$ drop argsToDrop e') :<: ty')
>     

To distill an elimination, we simply push the eliminator on to the spine.

> distillInfer es (t :$ e) as    = distillInfer es t (e : as)

Because there are no operators in the display syntax, we replace them with
parameters containing the appropriate primitive references.

> distillInfer es (op :@ ts) as  = distillInfer es (P (mkRef op)) (map A ts ++ as)

Unnecessary type ascriptions can simply be dropped; this also ensures that shared
parameters are handled correctly when the head is a parameter. 

> distillInfer es (N t :? _) as  = distillInfer es t as

Otherwise, type ascriptions are converted into type casts and the spine of
eliminators is applied in its entirety.

> distillInfer es (t :? ty) as   = do
>     ty'  :=>: vty  <- distill es (SET :>: ty)
>     t'   :=>: vt   <- distill es (vty :>: t)
>     (e', ty'')     <- processArgs es (vt :<: vty) as
>     return ((DType ty' ::$ A t') $::$ e' :<: ty'')

If nothing matches, we are unable to distill this term, so we complain loudly.

> distillInfer _ tm _ = error ("distillInfer: can't cope with " ++ show tm)


The |processArgs| command takes a list of entries in scope, a typed value
and a spine of arguments for the value. It distills the spine, using
|elimTy| to determine the appropriate type to push in at each step, and returns
the distilled spine and the overall type of the application.

> processArgs :: Entries -> (VAL :<: TY) -> Spine {TT} REF -> ProofStateT INTM (DSpine RelName, TY)
> processArgs _ (_ :<: ty) [] = return ([], ty)
> processArgs es (v :<: C ty) (a:as) = do
>     (e', ty') <- {- mliftError $ -} elimTy (distill es) (v :<: ty) a
>     (es, ty'') <- processArgs es (v $$ (fmap valueOf e') :<: ty') as 
>     return (fmap termOf e' : es, ty'')


The |toExDTm| helper function will distill a term to produce an
|Ex| representation by applying a type-cast if necessary.

> toExDTm :: Entries -> (INTM :>: INTM) -> ProofStateT INTM ExDTmRN
> toExDTm es (_ :>: N tm) = do
>     (tm' :<: _) <- distillInfer es tm []
>     return tm'
> toExDTm es (ty :>: tm) = do
>     (ty'  :=>: tyv)  <- distill es (SET :>: ty)
>     (tm'  :=>: _)    <- distill es (tyv :>: tm)
>     return (DTY ty' tm')
