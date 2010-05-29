\section{Distillation}
\label{sec:distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Distiller where

> import Control.Applicative
> import Control.Monad.State
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ (Doc)

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Developments
> import ProofState.ProofState
> import ProofState.ProofContext
> import ProofState.ProofKit
> import ProofState.NameResolution

> import DisplayLang.DisplayTm
> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import NameSupply.NameSupplier

> import Evidences.Rules
> import Evidences.Tm
> import Evidences.Mangler

%endif


The distiller, like the elaborator, is organized on a |check|/|infer|
basis, following the type-checker implementation in
Section~\ref{subsec:type-checking}. |distill| mirrors |check|--
distilling |INTM|s, while |distillInfer| mirrors |infer| -- distilling
|EXTM|s.


\subsection{Distilling |INTM|s}

The |distill| command converts a typed |INTM| in the Evidence language
to a term in the Display language; that is, it reverses |elaborate|.
It performs christening at the same time. For this, it needs a list of
entries in local(!) scope, which it will extend when going under a
binder.

\pierre{What is the ``local'' scope?}


The distiller first tries to apply Feature-specific rules. These rules
contain the inteligence of the distiller, aiming at making concise
Display term. If unsuccessful, the distiller fall back to a generic
distiller |distillBase|.

> distill :: Entries -> (TY :>: INTM) -> ProofStateT INTM (DInTmRN :=>: VAL)
> import <- DistillRules
> distill es tt = distillBase es tt

We separate out the standard distillation cases (without aspect
extensions) so that aspect distill rules can give up and invoke the
base cases.

> distillBase :: Entries -> (TY :>: INTM) -> ProofStateT INTM (DInTmRN :=>: VAL)

We distill structurally through canonical terms:

> distillBase es (C ty :>: C c) = do
>     cc <- canTy (distill es) (ty :>: c)
>     return $ (DC $ fmap termOf cc) :=>: evTm (C c)

To distill a $lambda$-abstraction, we speculate a fresh reference and distill
under the binder, then convert the scope appropriately.

> distillBase es (ty :>: l@(L sc)) = do
>     let x = fortran l
>     (k, dom, cod) <- lambdable ty `catchMaybe`  (err "distill: type " 
>                                                 ++ errVal ty 
>                                                 ++ err " is not lambdable.")
>     tm' :=>: _ <-  freshRef (x :<: dom) $ \ref ->
>                    distill  (es :< E  ref (lastName ref) (Boy k)
>                                       (error "distill: boy type undefined"))
>                             (cod (pval ref) :>: underScope sc ref)
>     return $ DL (convScope sc x tm') :=>: (evTm $ L sc)
>   where
>     convScope :: Scope {TT} REF -> String -> DInTmRN -> DSCOPE
>     convScope (_ :. _)  x  tm = x ::. tm
>     convScope (K _)     _  tm = DK tm

If we encounter a neutral term, we switch to |distillInfer|.

> distillBase es (_ :>: N n) = do
>     (n' :<: _) <- distillInfer es n []
>     return $ DN n' :=>: evTm n

If none of the cases match, we complain loudly.

> distillBase _ (ty :>: tm) =  throwError' $ 
>                              err "distill: can't cope with\n" ++
>                              errInTm tm ++ err " :<: " ++ errVal ty


\subsection{Distilling |EXTM|s}

The |distillInfer| command is the |EXTM| version of |distill|, which also yields
the type of the term. It keeps track of a list of entries in scope, but
also accumulates a spine so that shared parameters can be removed.

\pierre{What is a shared parameter? Why removing shared parameters?}

> distillInfer ::  Entries -> EXTM -> Spine {TT} REF -> 
>                  ProofStateT INTM (DExTmRN :<: TY)
>
> import <- DistillInferRules

To distill a parameter with a spine of eliminators, we use |baptise|
to determine a name for the reference and the number of shared
parameters, then process the arguments and return the distilled
application with the shared parameters dropped.

> distillInfer localEntries tm@(P (name := kind :<: ty)) spine = do
>     -- Compute a relative name from |name|
>     proofCtxt <- get
>     let  (relName, argsToDrop, mSch) = 
>           unresolve name kind spine (inBScope proofCtxt) localEntries
>     -- Distill the spine
>     (e', ty') <- distillSpine localEntries (evTm tm :<: ty) spine
>     let  spine1  = drop argsToDrop e'
>          spine2  = maybe spine1 (hideImplicit spine1) mSch 
>     return $ (DP relName ::$ spine2) :<: ty'
>   where
>     hideImplicit :: DSPINE -> Scheme x -> DSPINE
>     hideImplicit as      (SchType _)            = as
>     hideImplicit (a:as)  (SchExplicitPi _ sch)  = a : hideImplicit as sch
>     hideImplicit (a:as)  (SchImplicitPi _ sch)  = hideImplicit as sch
>     hideImplicit []      _                      = []

To distill an elimination, we simply push the eliminator on to the spine.

> distillInfer es (t :$ e) as    = distillInfer es t (e : as)

Because there are no operators in the display syntax, we replace them with
parameters containing the appropriate primitive references.

> distillInfer es (op :@ ts) as  = distillInfer es (P (lookupOpRef op))
>                                                      (map A ts ++ as)

Unnecessary type ascriptions can simply be dropped; this also ensures
that shared parameters are handled correctly when the head is a
parameter.

> distillInfer es (N t :? _) as  = distillInfer es t as

Type ascriptions that were inserted by elaboration of type casts can be removed,
if we are lucky, to give nicer output.

> distillInfer es (L ("typecast" :. NV 0) :? PI ty _) ((A a):as) =
>     distillInfer es (a :? ty) as

Otherwise, type ascriptions are converted into type casts and the spine of
eliminators is applied in its entirety.

> distillInfer es (t :? ty) as   = do
>     ty'  :=>: vty  <- distill es (SET :>: ty)
>     t'   :=>: vt   <- distill es (vty :>: t)
>     (e', ty'')     <- distillSpine es (vt :<: vty) as
>     return (DType ty' ::$ (A t' : e') :<: ty'')

If nothing matches, we are unable to distill this term, so we complain loudly.

> distillInfer _ tm _ =  throwError' $ 
>                        err "distillInfer: can't cope with " ++ errTm (N tm)



\subsection{Moonshining}

The |moonshine| command attempts the dubious task of converting an
evidence term (possibly of dubious veracity) into a display term.
This is mostly for error-message generation.

> moonshine :: INTM -> ProofStateT INTM DInTmRN
> moonshine (LK t) = do
>     t' <- moonshine t
>     return $ DLK t'
> moonshine (L (x :. t)) = do
>     t' <- moonshine t
>     return $ DL (x ::. t')
> moonshine (C c) = do
>     c' <- traverse moonshine c
>     return $ DC c'
> moonshine (N n) = (do
>     n' :<: ty <- distillInfer B0 n []
>     return $ DN n'
>   ) <|> return (DTIN (N n))
> moonshine t = return (DTIN t)



\subsection{Distillation Support}

The |distillSpine| command takes a list of entries in scope, a typed value
and a spine of arguments for the value. It distills the spine, using
|elimTy| to determine the appropriate type to push in at each step, and returns
the distilled spine and the overall type of the application.

> distillSpine :: Entries -> (VAL :<: TY) -> Spine {TT} REF -> ProofStateT INTM (DSPINE, TY)
> distillSpine _ (_ :<: ty) [] = return ([], ty)
> distillSpine es (v :<: C ty) (a:as) = do
>     (e', ty') <- elimTy (distill es) (v :<: ty) a
>     (es, ty'') <- distillSpine es (v $$ (fmap valueOf e') :<: ty') as 
>     return (fmap termOf e' : es, ty'')
> distillSpine es (v :<: ty) as = throwError' $
>     err "distillSpine: cannot cope with" ++ errTyVal (v :<: ty)
>     ++ err "which has non-canonical type" ++ errTyVal (ty :<: SET)
>     ++ err "applied to spine" ++ map UntypedElim as

The |toDExTm| helper function will distill a term to produce an
|Ex| representation by applying a type-cast if necessary.

> toDExTm :: Entries -> (INTM :>: INTM) -> ProofStateT INTM DExTmRN
> toDExTm es (_ :>: N tm) = do
>     (tm' :<: _) <- distillInfer es tm []
>     return tm'
> toDExTm es (ty :>: tm) = do
>     (ty'  :=>: tyv)  <- distill es (SET :>: ty)
>     (tm'  :=>: _)    <- distill es (tyv :>: tm)
>     return (DTY ty' tm')


\subsection{Distilling Schemes}

> distillScheme :: Entries -> Bwd REF -> Scheme INTM -> ProofStateT INTM (Scheme DInTmRN, INTM)

> distillScheme es rs (SchType ty) = do
>     let ty' = underneath 0 rs ty
>     ty'' :=>: _ <- distill es (SET :>: ty')
>     return (SchType ty'', ty')

> distillScheme es rs (SchExplicitPi (x :<: schS) schT) = do
>     (schS', s') <- distillScheme es rs schS
>     freshRef (x :<: evTm s')(\ref -> do
>         (schT', t') <- distillScheme (es :< E ref (lastName ref) (Boy PIB) s')
>                            (rs :< ref) schT
>         return (SchExplicitPi (x :<: schS') schT', PIV x s' t')
>       )

> distillScheme es rs (SchImplicitPi (x :<: s) schT) = do
>     let s' = underneath 0 rs s
>     sd :=>: sv <- distill es (SET :>: s')
>     freshRef (x :<: sv) (\ref -> do
>         (schT', t') <- distillScheme (es :< E ref (lastName ref) (Boy PIB) s')
>                            (rs :< ref) schT
>         return (SchImplicitPi (x :<: sd) schT', PIV x s' t')
>       )


> underneath :: Int -> Bwd REF -> INTM -> INTM
> underneath _ B0 tm = tm
> underneath n (rs :< ref) tm = underneath (n+1) rs (under n ref %% tm)




The |distillHere| command distills a term in the current context.

> distillHere :: (TY :>: INTM) -> ProofState (DInTmRN :=>: VAL)
> distillHere tt = do
>     mliftError $ distill B0 tt
>         where mliftError :: ProofStateT INTM a -> ProofState a
>               mliftError = mapStateT liftError

> distillSchemeHere :: Scheme INTM -> ProofState (Scheme DInTmRN)
> distillSchemeHere sch = do
>     return . fst =<< (mapStateT liftError $ distillScheme B0 B0 sch)


The |prettyHere| command distills a term in the current context,
then passes it to the pretty-printer.

> prettyHere :: (TY :>: INTM) -> ProofState Doc
> prettyHere = prettyHereAt maxBound

> prettyHereAt :: Size -> (TY :>: INTM) -> ProofState Doc
> prettyHereAt size tt = do
>     dtm :=>: _ <- distillHere tt
>     return (pretty dtm size)

> prettySchemeHere :: Scheme INTM -> ProofState Doc
> prettySchemeHere sch = do
>     sch' <- distillSchemeHere sch
>     return (pretty sch' maxBound)
