\section{The distiller}
\label{sec:distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Distiller where

> import Control.Monad.State
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
Section~\ref{subsec:type-checking}. |distill| mirrors |check| --
distilling |INTM|s, while |distillInfer| mirrors |infer| -- distilling
|EXTM|s.


\subsection{Distilling |INTM|s}
\label{subsec:distiller-intm}

The |distill| command converts a typed |INTM| in the Evidence language
to a term in the Display language; that is, it reverses |elaborate|.
It peforms christening at the same time, turning absolute names into
relative names. 

The distiller first tries to apply Feature-specific rules. These rules
contain the inteligence of the distiller, aiming at making concise
Display term. If unsuccessful, the distiller fall back to a generic
distiller |distillBase|.

When going under a binder, we have to introduce fresh names to distill
further. When christening, these fresh names have to be dealt with
separately (See |unresolve| in Section~\ref{subsec:christening}):
indeed, they are actually bound variables. Hence, we collect this
\emph{local scope} as a list of |entries|.

> distill :: Entries -> (TY :>: INTM) -> ProofStateT INTM (DInTmRN :=>: VAL)
> import <- DistillRules
> distill entries tt = distillBase entries tt

We separate out the standard distillation cases (without aspect
extensions) so that aspect distill rules can give up and invoke the
base cases.

> distillBase :: Entries -> (TY :>: INTM) -> ProofStateT INTM (DInTmRN :=>: VAL)

We distill structurally through canonical terms:

> distillBase entries (C ty :>: C c) = do
>     cc <- canTy (distill entries) (ty :>: c)
>     return $ (DC $ fmap termOf cc) :=>: evTm (C c)

To distill a $lambda$-abstraction, we speculate a fresh reference and distill
under the binder, then convert the scope appropriately.

\pierre{Why do we put an |error| for the entry type here and not in
       the equivalent place in @Distillation/Scheme@?}

> distillBase entries (ty :>: l@(L sc)) = do
>     let x = fortran l
>     (kind, dom, cod) <- lambdable ty `catchMaybe`  (err "distill: type " 
>                                                    ++ errVal ty 
>                                                    ++ err " is not lambdable.")
>     tm' :=>: _ <-  freshRef (x :<: dom) $ \ref ->
>                    distill  (entries :< E  ref (lastName ref) (Boy kind) 
>                                            (error "distill: type undefined"))
>                             (cod (pval ref) :>: underScope sc ref)
>     return $ DL (convScope sc x tm') :=>: (evTm $ L sc)
>   where
>     convScope :: Scope {TT} REF -> String -> DInTmRN -> DSCOPE
>     convScope (_ :. _)  x  tm = x ::. tm
>     convScope (K _)     _  tm = DK tm

If we encounter a neutral term, we switch to |distillInfer|.

> distillBase entries (_ :>: N n) = do
>     (n' :<: _) <- distillInfer entries n []
>     return $ DN n' :=>: evTm n

If none of the cases match, we complain loudly.

> distillBase _ (ty :>: tm) =  throwError' $ 
>                              err "distill: can't cope with\n" ++
>                              errInTm tm ++ err " :<: " ++ errVal ty


\subsection{Distilling |EXTM|s}

The |distillInfer| command is the |EXTM| version of |distill|, which
also yields the type of the term. Following |distill|, we maintain the
local scope of fresh references. 

Moreover, recall that the |DExTm| terms are in Spine form: they are
composed of a |DHead| -- either parameter, type annotation, or
embedding of |ExTm| -- and followed by a spine of eliminators. To
perform this translation, we accumulate a |spine| and discharge it as
late as possible. Doing so, shared parameters can be removed(?)

\pierre{What is a shared parameter? Why removing shared parameters?}

> distillInfer ::  Entries -> EXTM -> Spine {TT} REF -> 
>                  ProofStateT INTM (DExTmRN :<: TY)
>
> import <- DistillInferRules

To distill a parameter with a spine of eliminators, we use |baptise|
to determine a name for the reference and the number of shared
parameters, then process the arguments and return the distilled
application with the shared parameters dropped.

\pierre{The comment above makes little sense and seems to be
        outdated.}

> distillInfer entries tm@(P (name := kind :<: ty)) spine = do
>     -- Compute a relative name from |name|
>     proofCtxt <- get
>     let  (relName, argsToDrop, mSch) = 
>           unresolve name kind spine (inBScope proofCtxt) entries
>     -- Distill the spine
>     (e', ty') <- distillSpine entries (evTm tm :<: ty) spine
>     -- \pierre{And then\ldots no clue.}
>     let  spine1  = drop argsToDrop e'
>          spine2  = maybe spine1 (hideImplicit spine1) mSch 
>     -- Return the relative name applied to the simplified spine
>     return $ (DP relName ::$ spine2) :<: ty'
>   where
>     hideImplicit :: DSPINE -> Scheme x -> DSPINE
>     hideImplicit as      (SchType _)            = as
>     hideImplicit (a:as)  (SchExplicitPi _ sch)  = a : hideImplicit as sch
>     hideImplicit (a:as)  (SchImplicitPi _ sch)  = hideImplicit as sch
>     hideImplicit []      _                      = []

To distill an elimination, we simply push the eliminator on to the spine.

> distillInfer entries (t :$ e) spine = distillInfer entries t (e : spine)

Because there are no operators in the display syntax, we replace them with
parameters containing the appropriate primitive references.

> distillInfer entries (op :@ args) spine = 
>     distillInfer  entries (P  (lookupOpRef op)) (map A args ++ spine)

Unnecessary type ascriptions can simply be dropped. As we can always
\emph{infer} the type of a neutral term, there is no point in keeping
its ascription. This also ensures that shared parameters are handled
correctly when the head is a parameter.

\pierre{Why are shared parameters handled correctly in that case?}

> distillInfer entries (N t :? _) spine  = distillInfer entries t spine

Type ascriptions that were inserted by elaboration of type annotations
can be removed, if we are lucky, to give nicer output.

\pierre{Can't we match on any name, not just |"typeAnnot"|? If not, then
        maybe a less-likely to happen name would be good, stored in a
        variable somewhere.}

> distillInfer entries (L ("typeAnnot" :. NV 0) :? PI ty _) ((A a):spine) =
>     distillInfer entries (a :? ty) spine

Otherwise, we have no choice but distilling both side of the type
ascription (term and value). This gives a type annotation applied to
the distilled term, together with the distilled spine.

> distillInfer entries (t :? ty) spine   = do
>     -- Distill the type
>     ty1  :=>: vty  <- distill entries (SET :>: ty)
>     -- Distill the term
>     t1   :=>: vt   <- distill entries (vty :>: t)
>     -- Distill the spine
>     (e, ty2)     <- distillSpine entries (vt :<: vty) spine
>     -- Annotate the term by the type, followed by its spine
>     return $ DType ty1 ::$ (A t1 : e) :<: ty2

If nothing matches, we are unable to distill this term, so we complain loudly.

> distillInfer _ tm _ =  throwError' $ 
>                        err "distillInfer: can't cope with " ++ errTm (N tm)


\subsection{Distillation Support}

The |distillSpine| command takes a list of entries in scope, a typed value
and a spine of arguments for the value. It distills the spine, using
|elimTy| to determine the appropriate type to push in at each step, and returns
the distilled spine and the overall type of the application.

> distillSpine ::  Entries -> (VAL :<: TY) -> Spine {TT} REF -> 
>                  ProofStateT INTM (DSPINE, TY)
> distillSpine _        (_ :<: ty)    []         = return ([], ty)
> distillSpine entries  (v :<: C ty)  (a:spine)  = do
>     -- Distill structurally the eliminator |a|
>     (e1, ty1) <- elimTy (distill entries) (v :<: ty) a
>     -- Further distill the spine
>     (es, ty2) <- distillSpine entries (v $$ (fmap valueOf e1) :<: ty1) spine
>     -- Return distilled spine and type of the application
>     return (fmap termOf e1 : es, ty2)
> distillSpine entries  (v :<: ty)    spine      = throwError' $
>     err "distillSpine: cannot cope with" ++ errTyVal (v :<: ty)
>     ++ err "which has non-canonical type" ++ errTyVal (ty :<: SET)
>     ++ err "applied to spine" ++ map UntypedElim spine


The |toDExTm| helper function will distill a term to produce an |Ex|
representation by applying a type annotation only if necessary.

> toDExTm :: Entries -> (INTM :>: INTM) -> ProofStateT INTM DExTmRN
> toDExTm entries (_ :>: N tm) = do
>     (tm' :<: _) <- distillInfer entries tm []
>     return tm'
> toDExTm entries (ty :>: tm) = do
>     (ty'  :=>: tyv)  <- distill entries (SET :>: ty)
>     (tm'  :=>: _)    <- distill entries (tyv :>: tm)
>     return $ DTY ty' tm'


\subsection{Distillation interface}

The |distillHere| command distills a term in the current context.

> distillHere :: (TY :>: INTM) -> ProofState (DInTmRN :=>: VAL)
> distillHere tt = mapStateT liftError $ distill B0 tt

The |prettyHere| command distills a term in the current context,
then passes it to the pretty-printer.

> prettyHere :: (TY :>: INTM) -> ProofState Doc
> prettyHere = prettyHereAt maxBound

> prettyHereAt :: Size -> (TY :>: INTM) -> ProofState Doc
> prettyHereAt size tt = do
>     dtm :=>: _ <- distillHere tt
>     return (pretty dtm size)



