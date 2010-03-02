\section{Using the |Elab| language}
\label{sec:make_elab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Elaboration.MakeElab where

> import Control.Monad.Error

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features ()

> import ProofState.ProofKit

> import DisplayLang.DisplayTm

> import Elaboration.ElabMonad

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\subsection{Tools for writing elaborators}

When part of the display syntax needs to be elaborated as a subproblem, we call
|subElab| rather than |makeElab| to ensure the elaboration does not take place
at the top level. This means that if the subproblem needs to modify the proof
state (for example, to introduce a $\lambda$-boy) it will create a new girl
to work in.

> subElab :: Loc -> (TY :>: InDTmRN) -> Elab (INTM :=>: VAL)
> subElab loc (ty :>: tm) = eElab loc (ty :>: ElabProb tm)

> internalElab :: Loc -> (TY :>: EProb) -> Elab (INTM :=>: VAL)
> internalElab loc (ty :>: ElabDone tt)                = return tt
> internalElab loc (ty :>: ElabProb tm)                = makeElab loc (ty :>: tm)
> internalElab loc (ty :>: ElabInferProb tm)           = makeElabInfer loc tm
> internalElab loc (ty :>: WaitCan (_ :=>: C _) prob)  = internalElab loc (ty :>: prob)
> internalElab loc (ty :>: prob)                       = eElab loc (ty :>: prob)


The |eCan| instruction asks for an elaboration problem to be solved when the
supplied value is canonical, and returns the result of solving the problem
(which may well be a suspended definition if the value is not currently canonical).

> eCan :: INTM :=>: VAL -> (TY :>: EProb) -> Elab (INTM :=>: VAL)
> eCan tt (ty :>: prob) = internalElab (Loc 0) (ty :>: WaitCan tt prob)


We can type-check a term using the |eCheck| instruction.

> eCheck :: (TY :>: INTM) -> Elab (INTM :=>: VAL)
> eCheck tytm = do
>     nsupply <- eAskNSupply
>     case liftError (typeCheck (check tytm) nsupply) of
>         Left e    -> throwError e
>         Right tt  -> return tt


The |eCoerce| instruction attempts to coerce a value from the first type to
the second type, either trivially (if the types are definitionally equal) or by
hoping for a proof of the appropriate equation and inserting a coercion.

> eCoerce :: INTM :=>: VAL -> INTM :=>: VAL -> INTM :=>: VAL -> Elab (INTM :=>: VAL)
> eCoerce (_S :=>: _Sv) (_T :=>: _Tv) (s :=>: sv) = do
>     eq <- eEqual $ SET :>: (_Sv, _Tv)
>     if eq
>         then return (s :=>: sv)
>         else do
>             q :=>: qv <- eHope $ PRF (EQBLUE (SET :>: _Sv) (SET :>: _Tv))
>             return $ N (coe :@ [_S, _T, q, s]) :=>: coe @@ [_Sv, _Tv, qv, sv]


The |elabEnsure| instruction demands that a value should be equal to a canonical
value with the given shape. It returns a term and value with the required shape,
together with a proof that these equal the input.

> elabEnsure :: INTM :=>: VAL -> (Can VAL :>: Can ()) -> Elab (INTM :=>: Can VAL, INTM :=>: VAL)
> elabEnsure (tm :=>: C v) (ty :>: t) = case halfZip v t of
>     Nothing  -> throwError' $ err "elabEnsure: halfZip failed!"
>     Just _   -> do
>         ty' :=>: _ <- eQuote (C ty)
>         return (tm :=>: v, N (P refl :$ A ty' :$ A tm)
>                                  :=>: pval refl $$ A (C ty) $$ A (C v))
> elabEnsure (_ :=>: L _) _ = throwError' $ err "elabEnsure: failed to match lambda!"
> elabEnsure (_ :=>: nv) (ty :>: t) = do
>     vu <- unWrapElab $ canTy chev (ty :>: t)
>     let v = fmap valueOf vu
>     pp <- eHope . PRF $ EQBLUE (C ty :>: nv) (C ty :>: C v)
>     return (C (fmap termOf vu) :=>: v, pp)
>  where
>    chev :: (TY :>: ()) -> WrapElab (INTM :=>: VAL)
>    chev (ty :>: ()) = WrapElab (eHope ty)


The |eEqual| instruction determines if two types are definitionally equal.

> eEqual :: (TY :>: (VAL, VAL)) -> Elab Bool
> eEqual tyvv = do
>     nsupply <- eAskNSupply
>     return (equal tyvv nsupply)


The |eInfer| instruction infers the type of an evidence term.

> eInfer :: EXTM -> Elab (INTM :=>: VAL)
> eInfer tm = do
>     nsupply <- eAskNSupply
>     case liftError (typeCheck (infer tm) nsupply) of
>         Left e    -> throwError e
>         Right (tv :<: ty)  -> do
>             ty' :=>: _ <- eQuote ty
>             return $ PAIR ty' (N tm) :=>: PAIR ty tv


The |eQuote| instruction $\beta$-quotes a value to produce a term representation.

> eQuote :: VAL -> Elab (INTM :=>: VAL)
> eQuote v = do
>     nsupply <- eAskNSupply
>     return (bquote B0 v nsupply :=>: v)


\subsection{Elaborating |InDTm|s}

We can use the |Elab| language to describe how to elaborate a display term to
produce an evidence term.

> makeElab :: Loc -> (TY :>: InDTmRN) -> Elab (INTM :=>: VAL)

> import <- MakeElabRules

These rules should be moved to features.

> makeElab loc (SET :>: DIMU Nothing iI d i) = do
>       l :=>: lv <- eFake False
>       iI :=>: iIv <- subElab loc (SET :>: iI)
>       d :=>: dv <- subElab loc (ARR iIv (IDESC iIv) :>: d)
>       i :=>: iv <- subElab loc (iIv :>: i)

\question{What is this check for, and how can we implement it in |Elab|?}

<       lastIsIndex <- eEqual (SET :>: (iv,N (P (last xs))))
<       guard lastIsIndex
<       -- should check i doesn't appear in d (fairly safe it's not in iI :))

>       return $ IMU (Just (N l)) iI d i :=>: IMU (Just lv) iIv dv iv

> makeElab loc (PI UNIT t :>: DCON f) = do
>     tm :=>: tmv <- subElab loc (t $$ A VOID :>: f)
>     return $ LK tm :=>: LK tmv

> makeElab loc (PI (MU l d) t :>: DCON f) = do
>     d' :=>: _ <- eQuote d
>     t' :=>: _ <- eQuote t
>     tm :=>: tmv <- subElab loc $ case l of
>         Nothing  -> elimOpMethodType $$ A d $$ A t :>: f
>         Just l   -> elimOpLabMethodType $$ A l $$ A d $$ A t :>: f
>     x <- eLambda (fortran t)
>     return $ N (elimOp :@ [d', NP x, t', tm]) :=>: elimOp @@ [d, NP x, t, tmv]

> makeElab loc (PI (SIGMA d r) t :>: DCON f) = do
>     let mt =  PI d . L . HF (fortran r) $ \ a ->
>               PI (r $$ A a) . L . HF (fortran t) $ \ b ->
>               t $$ A (PAIR a b)
>     mt' :=>: _ <- eQuote mt
>     tm :=>: tmv <- subElab loc (mt :>: f)
>     x <- eLambda (fortran t)
>     return $ N ((tm :? mt') :$ A (N (P x :$ Fst)) :$ A (N (P x :$ Snd)))
>                     :=>: tmv $$ A (NP x $$ Fst) $$ A (NP x $$ Snd)

> makeElab loc (PI (ENUMT e) t :>: m) | isTuply m = do
>     t' :=>: _ <- eQuote t
>     e' :=>: _ <- eQuote e
>     tm :=>: tmv <- subElab loc (branchesOp @@ [e, t] :>: m)
>     x <- eLambda (fortran t)
>     return $ N (switchOp :@ [e', NP x, t', tm]) :=>: switchOp @@ [e, NP x, t, tmv]
>   where
>     isTuply :: InDTmRN -> Bool
>     isTuply DVOID        = True
>     isTuply (DPAIR _ _)  = True
>     isTuply _            = False

> makeElab loc (MONAD d x :>: DCON t) = makeElab loc (MONAD d x :>: DCOMPOSITE t)
> makeElab loc (QUOTIENT a r p :>: DPAIR x DVOID) =
>   makeElab loc (QUOTIENT a r p :>: DCLASS x)

> makeElab loc (NU d :>: DCOIT DU sty f s) = do
>   d' :=>: _ <- eQuote d
>   makeElab loc (NU d :>: DCOIT (DTIN d') sty f s)



We use underscores |DU| in elaboration to mean "figure this out yourself".

> makeElab loc (ty :>: DU) = eHope ty
> makeElab loc (ty :>: DQ s) = EWait s ty neutralise


Elaborating a canonical term with canonical type is a job for |canTy|.

> makeElab loc (C ty :>: DC tm) = do
>     v <- canTy (subElab loc) (ty :>: tm)
>     return $ (C $ fmap termOf v) :=>: (C $ fmap valueOf v)


There are a few possibilities for elaborating $\lambda$-abstractions. If both the
range and term are constants, then we simply |makeElab| underneath. This avoids
creating some trivial children. 

> makeElab loc (PI s (L (K t)) :>: DL (DK dtm)) = do
>     tm :=>: tmv <- subElab loc (t :>: dtm)
>     return $ LK tm :=>: LK tmv

Otherwise, we can simply create a |lambdaBoy| in the current
development, and carry on elaborating.

> makeElab loc (ty :>: DL sc) = do
>     ref <- eLambda (dfortran (DL sc))
>     ty' <- eGoal
>     makeElab loc (ty' :>: dScopeTm sc)


We push types in to neutral terms by calling |makeElabInfer| on the term, then
coercing the result to the required type. (Note that |eCoerce| will check if the
types are equal, and if so it will not insert a redundant coercion.)

> makeElab loc (w :>: DN n) = do
>     w' :=>: _ <- eQuote w
>     tt <- makeElabInfer loc n
>     let (yt :=>: yn :<: ty :=>: tyv) = extractNeutral tt
>     eCoerce (ty :=>: tyv) (w' :=>: w) (yt :=>: yn)


If we already have an evidence term, we just have to type-check it.

> makeElab loc (ty :>: DTIN tm) = eCheck (ty :>: tm)


If the type is neutral and none of the preceding cases match,
there is nothing we can do but wait for the type to become canonical.

> makeElab loc (N ty :>: tm) = do
>     tt <- eQuote (N ty)
>     eCan tt (N ty :>: ElabProb tm)


If nothing else matches, give up and report an error.

> makeElab loc (ty :>: tm) = throwError' $ err "makeElab: can't push"
>     ++ errTyVal (ty :<: SET) ++ err "into" ++ errTm tm 


\subsection{Elaborating |ExDTm|s}

The |makeElabInfer| command is to |infer| in subsection~\ref{subsec:type-inference} 
as |makeElab| is to |check|. It elaborates the display term and infers its type
to produce a type-term pair in the evidence language.

> makeElabInfer :: Loc -> ExDTmRN -> Elab (INTM :=>: VAL)

> makeElabInfer loc (t ::$ ss) = do
>     (tt, ms) <- makeElabInferHead loc t
>     let (tm :=>: tmv :<: ty :=>: tyv) = extractNeutral tt
>     case ms of
>         Just sch  -> handleSchemeArgs B0 sch  (tm :? ty :=>: tmv :<: tyv) ss
>         Nothing   -> handleArgs               (tm :? ty :=>: tmv :<: tyv) ss
>   where
>     handleSchemeArgs :: Bwd (INTM :=>: VAL) -> Scheme INTM -> (EXTM :=>: VAL :<: TY)
>         -> DSpine RelName -> Elab (INTM :=>: VAL)
>     handleSchemeArgs es (SchType _) (tm :=>: tv :<: ty) [] = do
>         ty' :=>: _ <- eQuote ty
>         return $ PAIR ty' (N tm) :=>: PAIR ty tv
>     handleSchemeArgs es (SchExplicitPi (x :<: schS) schT) (tm :=>: tv :<: PI sd t) [] = do
>         let sv = eval (schemeToInTm schS) (fmap valueOf es)
>         tm :=>: tv <- eCompute
>             (PI sv (L . HF x . const $ sigSetVAL) :>: do
>                 ref <- eLambda x
>                 handleSchemeArgs (es :< (NP ref :=>: NP ref)) schT
>                     (tm :$ A (NP ref) :=>: tv $$ A (NP ref) :<: t $$ A (NP ref)) []
>             )
>         s' :=>: _ <- eQuote sv
>         let  atm  = tm :? PIV x s' sigSetTM :$ A (NV 0)
>              rtm  = PAIR (PIV x s' (N (atm :$ Fst))) (LAV x (N (atm :$ Snd)))
>         return $ rtm :=>: evTm rtm
>     handleSchemeArgs es (SchExplicitPi (x :<: schS) schT) (tm :=>: tv :<: PI sd t) (A a : as) = do
>         let s' = schemeToInTm schS
>         atm :=>: av <- subElab loc (eval s' (fmap valueOf es) :>: a)
>         handleSchemeArgs (es :< (atm :=>: av)) schT (tm :$ A atm :=>: tv $$ A av :<: t $$ A av) as
>     handleSchemeArgs es (SchImplicitPi (x :<: s) schT) (tm :=>: tv :<: PI sd t) as = do
>         stm :=>: sv <- eHope (eval s (fmap valueOf es))
>         handleSchemeArgs (es :< (stm :=>: sv)) schT (tm :$ A stm :=>: tv $$ A sv :<: t $$ A sv) as
>     handleSchemeArgs _ _ (t :=>: v :<: C cty) (a : as) = do
>         (a', ty') <- elimTy (subElab loc) (v :<: cty) a
>         handleArgs (t :$ fmap termOf a' :=>: v $$ fmap valueOf a' :<: ty') as

>     handleArgs :: (EXTM :=>: VAL :<: TY) -> DSpine RelName -> Elab (INTM :=>: VAL)
>     handleArgs (tm :=>: tv :<: ty) [] = do
>         ty' :=>: _ <- eQuote ty
>         return $ PAIR ty' (N tm) :=>: PAIR ty tv
>     handleArgs (t :=>: v :<: C cty) (a : as) = do
>         (a', ty') <- elimTy (subElab loc) (v :<: cty) a
>         handleArgs (t :$ fmap termOf a' :=>: v $$ fmap valueOf a' :<: ty') as

<     handleArgs (tm :=>: tv :<: ty) (A a : as) = do
<         ty' :=>: _ <- eQuote ty
<         (cty :=>: ctyv, q :=>: qv) <- elabEnsure (ty' :=>: ty) (Set :>: Pi () ())
<         handleArgs (coe :@ [ty', cty, q, N tm] :=>: coe @@ [ty, C ctyv, qv, tv] :<: C ctyv) (A a : as)

>     handleArgs (tm :=>: tv :<: ty) as = do
>         tt <- eQuote ty
>         eCan tt (sigSetVAL :>: ElabInferProb (DTEX tm ::$ as))

> makeElabInferHead :: Loc -> DHead RelName -> Elab (INTM :=>: VAL, Maybe (Scheme INTM))

> makeElabInferHead loc (DP rn) = eResolve rn

> makeElabInferHead loc (DType ty) = do
>     tm :=>: tmv <- subElab loc (SET :>: ty)
>     return (PAIR (ARR tm tm) (idTM "typecast")
>                  :=>: PAIR (ARR tmv tmv) (idVAL "typecast")
>            , Nothing)

> makeElabInferHead loc (DTEX tm) = do
>     tt <- eInfer tm
>     return (tt, Nothing)

> makeElabInferHead loc tm = throwError' $ err "makeElabInferHead: can't cope with"
>     ++ errTm (DN (tm ::$ []))


The result of |makeElabInfer| is of type $\Sigma X \!\! : \!\! Set . X$, which we can
represent as an evidence term or value (|sigSetTM| or |sigSetVAL|, respectively).

> sigSetTM :: INTM
> sigSetTM = SIGMA SET (idTM "sst")

> sigSetVAL :: VAL
> sigSetVAL = SIGMA SET (idVAL "ssv")


The |extractNeutral| function separates type-term pairs in both term and value forms.
It avoids clutter in the term representation by splitting it up if it happens to be
a canonical pair, or applying the appropriate eliminators if not.

> extractNeutral :: INTM :=>: VAL -> INTM :=>: VAL :<: INTM :=>: TY
> extractNeutral (PAIR ty tm :=>: PAIR tyv tmv) = tm :=>: tmv :<: ty :=>: tyv
> extractNeutral (PAIR ty tm :=>: tv) = tm :=>: tv $$ Snd :<: ty :=>: tv $$ Fst
> extractNeutral (tm :=>: tv) = N (tm' :$ Snd) :=>: tv $$ Snd :<: N (tm' :$ Fst) :=>: tv $$ Fst
>   where tm' = tm :? sigSetTM