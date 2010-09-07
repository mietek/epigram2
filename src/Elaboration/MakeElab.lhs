\section{Using the |Elab| language}
\label{sec:Elaboration.MakeElab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Elaboration.MakeElab where

> import Control.Applicative
> import Control.Monad.Error

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.TypeChecker
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.BetaQuotation
> import Evidences.DefinitionalEquality
> import Evidences.Utilities

> import Features.Features ()

> import ProofState.Edition.ProofState

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme

> import Elaboration.ElabProb
> import Elaboration.ElabMonad

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\subsection{Tools for writing elaborators}

The |eCan| instruction asks for the current goal to be solved by the given
elaboration problem when the supplied value is canonical.

> eCan :: INTM :=>: VAL -> EProb -> Elab a
> eCan (_ :=>: C _)  prob = eElab (Loc 0) prob
> eCan tt            prob = eElab (Loc 0) (WaitCan (justEval tt) prob)


We can type-check a term using the |eCheck| instruction.

> eCheck :: (TY :>: INTM) -> Elab (INTM :=>: VAL)
> eCheck tytm = do
>     nsupply <- eAskNSupply
>     case liftError DTIN (typeCheck (check tytm) nsupply) of
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
>             q :=>: qv <- eHopeFor $ PRF (EQBLUE (SET :>: _Sv) (SET :>: _Tv))
>             return $ N (coe :@ [_S, _T, q, s]) :=>: coe @@ [_Sv, _Tv, qv, sv]


The |eEqual| instruction determines if two types are definitionally equal.

> eEqual :: (TY :>: (VAL, VAL)) -> Elab Bool
> eEqual tyvv = do
>     nsupply <- eAskNSupply
>     return (equal tyvv nsupply)


The |eHope| instruction hopes that the current goal can be solved.

> eHope :: Elab a
> eHope = eElab (Loc 0) ElabHope


The |eHopeFor| instruction hopes for an element of a type.

> eHopeFor :: TY -> Elab (INTM :=>: VAL)
> eHopeFor ty = eCompute (ty :>: eHope)


The |eInfer| instruction infers the type of an evidence term.

> eInfer :: EXTM -> Elab (INTM :=>: VAL)
> eInfer tm = do
>     nsupply <- eAskNSupply
>     case liftError DTIN (typeCheck (infer tm) nsupply) of
>         Left e    -> throwError e
>         Right (tv :<: ty)  -> do
>             ty' :=>: _ <- eQuote ty
>             return $ PAIR ty' (N tm) :=>: PAIR ty tv


The |eQuote| instruction $\beta$-quotes a value to produce a term representation.

> eQuote :: VAL -> Elab (INTM :=>: VAL)
> eQuote v = do
>     nsupply <- eAskNSupply
>     return (bquote B0 v nsupply :=>: v)


The |eSchedule| instruction asks for the scheduler to deal with other problems
before returning its result.

> eSchedule :: (INTM :=>: VAL) -> Elab a
> eSchedule (tm :=>: tv) = eElab (Loc 0) (ElabSchedule (ElabDone (tm :=>: Just tv)))


\subsection{Elaborating |DInTm|s}

We use the |Elab| language to describe how to elaborate a display term to
produce an evidence term. The |makeElab| and |makeElabInfer| functions read a
display term and use the capabilities of the |Elab| monad to produce a
corresponding evidence term. 

When part of the display syntax needs to be elaborated as a
subproblem, we call |subElab| or |subElabInfer| rather than |makeElab|
or |makeElabInfer| to ensure that elaboration does not take place at
the top level. This means that if the subproblem needs to modify the
proof state (for example, to introduce a $\lambda$) it will create a
new definition to work in. It also ensures that the subproblem can
terminate with the |eElab| instruction, providing a syntactic
representation.

> subElab :: Loc -> (TY :>: DInTmRN) -> Elab (INTM :=>: VAL)
> subElab loc (ty :>: tm) = eCompute (ty :>: makeElab loc tm)

> subElabInfer :: Loc -> DExTmRN -> Elab (INTM :=>: VAL)
> subElabInfer loc tm = eCompute (sigSetVAL :>: makeElabInfer loc tm)

Since we frequently pattern-match on the goal type when elaborating |In| terms,
we abstract it out. Thus |makeElab'| actually implements elaboration.

> makeElab :: Loc -> DInTmRN -> Elab (INTM :=>: VAL)
> makeElab loc tm = makeElab' loc . (:>: tm) =<< eGoal

> makeElab' :: Loc -> (TY :>: DInTmRN) -> Elab (INTM :=>: VAL)

> import <- MakeElabRules


We use underscores |DU| in elaboration to mean "figure this out yourself", while
question marks |DQ| require us to wait for a user-provided value.

> makeElab' loc (ty :>: DU) = eHope
> makeElab' loc (ty :>: DQ s) = eWait s ty >>= neutralise


Elaborating a canonical term with canonical type is a job for |canTy|.

> makeElab' loc (C ty :>: DC tm) = do
>     v <- canTy (subElab loc) (ty :>: tm)
>     return $ (C $ fmap termOf v) :=>: (C $ fmap valueOf v)


There are a few possibilities for elaborating $\lambda$-abstractions. If both the
range and term are constants, then we simply |makeElab| underneath. This avoids
creating some trivial children. 

> makeElab' loc (PI s (L (K t)) :>: DL (DK dtm)) = do
>     tm :=>: tmv <- subElab loc (t :>: dtm)
>     return $ LK tm :=>: LK tmv

Otherwise, we can simply create a |lambdaParam| in the current development, and
carry on elaborating. We can call |makeElab| here, rather than |subElab|,
because it is a tail call.

> makeElab' loc (ty :>: DL sc) = do
>     ref <- eLambda (dfortran (DL sc))
>     makeElab loc (dScopeTm sc)


We push types in to neutral terms by calling |subElabInfer| on the term, then
coercing the result to the required type. (Note that |eCoerce| will check if the
types are equal, and if so it will not insert a redundant coercion.)

> makeElab' loc (w :>: DN n) = do
>     w' :=>: _ <- eQuote w
>     tt <- subElabInfer loc n
>     let (yt :=>: yn :<: ty :=>: tyv) = extractNeutral tt
>     eCoerce (ty :=>: tyv) (w' :=>: w) (yt :=>: yn)


If we already have an evidence term, we just type-check it. This allows
elaboration code to partially elaborate a display term then embed the
resulting evidence term and call the elaborator again.

> makeElab' loc (ty :>: DTIN tm) = eCheck (ty :>: tm)


If the type is neutral and none of the preceding cases match,
there is nothing we can do but wait for the type to become canonical.

> makeElab' loc (N ty :>: tm) = do
>     tt <- eQuote (N ty)
>     eCan tt (ElabProb tm)


If nothing else matches, give up and report an error.

> makeElab' loc (ty :>: tm) = throwError' $ err "makeElab: can't push"
>     ++ errTyVal (ty :<: SET) ++ err "into" ++ errTm tm 


\subsection{Elaborating |DExTm|s}

The |makeElabInfer| command is to |infer| in
subsection~\ref{subsec:Evidences.TypeChecker.type-inference} as |makeElab|
is to |check|. It elaborates the display term and infers its type to
produce a type-term pair in the evidence language.

The result of |makeElabInfer| is of type $\SIGMA{\V{X}}{\Set}{X}$, which
we can represent as an evidence term or value (|sigSetTM| or |sigSetVAL|,
respectively).

> sigSetVAL :: Tm {In,p} x
> sigSetVAL = SIGMA SET (idVAL "ssv")

> sigSetTM :: INTM
> sigSetTM =  sigSetVAL 


The |extractNeutral| function separates type-term pairs in both term and value
forms. It avoids clutter in the term representation by splitting it up if it
happens to be a canonical pair, or applying the appropriate eliminators if not.

> extractNeutral :: INTM :=>: VAL -> INTM :=>: VAL :<: INTM :=>: TY
> extractNeutral (PAIR ty tm :=>: PAIR tyv tmv) = tm :=>: tmv :<: ty :=>: tyv
> extractNeutral (PAIR ty tm :=>: tv) = tm :=>: tv $$ Snd :<: ty :=>: tv $$ Fst
> extractNeutral (tm :=>: tv) = N (tm' :$ Snd) :=>: tv $$ Snd :<: N (tm' :$ Fst) :=>: tv $$ Fst
>   where tm' = tm ?? sigSetTM


Since we use a head-spine representation for display terms, we need to
elaborate the head of an application. The |makeElabInferHead| function
uses the |Elab| monad to produce a type-term pair for the head, and
provides its scheme (if it has one) for argument synthesis. The head
may be a parameter, which is resolved; an embedded evidence term,
which is checked; or a type annotation, which is converted to the
identity function at the given type.

> makeElabInferHead :: Loc -> DHEAD -> Elab (INTM :=>: VAL, Maybe (Scheme INTM))
> makeElabInferHead loc (DP rn)     = eResolve rn
> makeElabInferHead loc (DTEX tm)   = (| (eInfer tm) , ~Nothing |)
> makeElabInferHead loc (DType ty)  = do
>     tm :=>: v <- subElab loc (SET :>: ty)
>     return (typeAnnotTM tm :=>: typeAnnotVAL v, Nothing)
>   where
>     typeAnnotTM :: INTM -> INTM
>     typeAnnotTM tm = PAIR (ARR tm tm) (idTM "typeAnnot")
>     typeAnnotVAL :: VAL -> VAL
>     typeAnnotVAL v = PAIR (ARR v v) (idVAL "typeAnnot")


Now we can implement |makeElabInfer|. We use |makeElabInferHead| to elaborate
the head of the neutral term, then call |handleArgs| or |handleSchemeArgs| to
process the spine of eliminators.

> makeElabInfer :: Loc -> DExTmRN -> Elab (INTM :=>: VAL)
> makeElabInfer loc (t ::$ ss) = do
>     (tt, ms) <- makeElabInferHead loc t
>     let (tm :=>: tmv :<: ty :=>: tyv) = extractNeutral tt
>     case ms of
>         Just sch  -> handleSchemeArgs B0 sch  (tm ?? ty :=>: tmv :<: tyv) ss
>         Nothing   -> handleArgs               (tm ?? ty :=>: tmv :<: tyv) ss
>   where

The |handleSchemeArgs| function takes a list of terms (corresponding to
de Bruijn-indexed variables), the scheme, term and type of the neutral, and a
spine of eliminators in display syntax. It elaborates the eliminators and applies
them to the neutral term, using the scheme to handle insertion of implicit
arguments.

>     handleSchemeArgs :: Bwd (INTM :=>: VAL) -> Scheme INTM ->
>         EXTM :=>: VAL :<: TY -> DSPINE -> Elab (INTM :=>: VAL)

If the scheme is just a type, then we call on the non-scheme |handleArgs|.

>     handleSchemeArgs es (SchType _) ttt as = handleArgs ttt as

If the scheme has an implicit $\Pi$-binding, then we hope for a value of the
relevant type and carry on. Note that we evaluate the type of the binding in the
context |es|.

>     handleSchemeArgs es  (SchImplicitPi (x :<: s) schT)
>                              (tm :=>: tv :<: PI sd t) as = do
>         stm :=>: sv <- eHopeFor (eval s (fmap valueOf es, []))
>         handleSchemeArgs (es :< (stm :=>: sv)) schT
>             (tm :$ A stm :=>: tv $$ A sv :<: t $$ A sv) as

If the scheme has an explicit $\Pi$-binding and we have an argument, then we can
push the expected type into the argument and carry on.
\question{Does this case need to be modified for higher-order schemes?}

>     handleSchemeArgs es  (SchExplicitPi (x :<: schS) schT)
>                              (tm :=>: tv :<: PI sd t) (A a : as) = do
>         let s' = schemeToInTm schS
>         atm :=>: av <- subElab loc (eval s' (fmap valueOf es, []) :>: a)
>         handleSchemeArgs (es :< (atm :=>: av)) schT
>             (tm :$ A atm :=>: tv $$ A av :<: t $$ A av) as

If the scheme has an explicit $\Pi$-binding, but we have no more eliminators,
then we go under the binder and continue processing the scheme in order to
insert any implicit arguments that might be there. We then have to reconstruct
the overall type-term pair from the result.

>     handleSchemeArgs es  (SchExplicitPi (x :<: schS) schT)
>                              (tm :=>: tv :<: PI sd t) [] = do
>         let sv = eval (schemeToInTm schS) (fmap valueOf es, [])
>         tm :=>: tv <- eCompute
>             (PI sv (L $ K sigSetVAL) :>: do
>                 r <- eLambda x
>                 let rt = NP r
>                 handleSchemeArgs (es :< (rt :=>: rt)) schT
>                     (tm :$ A rt :=>: tv $$ A rt :<: t $$ A rt) []
>             )
>         s' :=>: _ <- eQuote sv
>         let  atm  = tm ?? PIV x s' sigSetTM :$ A (NV 0)
>              rtm  = PAIR (PIV x s' (N (atm :$ Fst))) (LAV x (N (atm :$ Snd)))
>         return $ rtm :=>: evTm rtm

Otherwise, we probably have a scheme with an explicit $\Pi$-binding but an
eliminator other than application, so we give up and throw an error. 

>     handleSchemeArgs es sch (_ :=>: v :<: ty) as = throwError' $
>         err "handleSchemeArgs: cannot handle scheme" ++ errScheme sch ++
>         err "with neutral term" ++ errTyVal (v :<: ty) ++
>         err "and eliminators" ++ map ErrorElim as


The |handleArgs| function is a simplified version of |handleSchemeArgs|, for
neutral terms without schemes. It takes a typed neutral term and a spine of
eliminators in display syntax, and produces a set-value pair in the |Elab| monad.

>     handleArgs :: (EXTM :=>: VAL :<: TY) -> DSPINE -> Elab (INTM :=>: VAL)

If we have run out of eliminators, then we just give back the neutral term with
its type.

>     handleArgs (tm :=>: tv :<: ty) [] = do
>         ty' :=>: _ <- eQuote ty
>         return $ PAIR ty' (N tm) :=>: PAIR ty tv

If we have a term of a labelled type being eliminated with |Call|, we need to
attach the appropriate label to the call and continue with the returned type.

>     handleArgs (t :=>: v :<: LABEL l ty) (Call _ : as) = do
>         l' :=>: _ <- eQuote l
>         handleArgs (t :$ Call l' :=>: v $$ Call l :<: ty) as

For all other eliminators, assuming the type is canonical we can use |elimTy|.

>     handleArgs (t :=>: v :<: C cty) (a : as) = do
>         (a', ty') <- elimTy (subElab loc) (v :<: cty) a
>         handleArgs (t :$ fmap termOf a' :=>: v $$ fmap valueOf a' :<: ty') as

Otherwise, we cannot do anything apart from waiting for the type to become
canonical, so we suspend elaboration and record the current problem.

>     handleArgs (tm :=>: tv :<: ty) as = do
>         tt <- eQuote ty
>         eCan tt (ElabInferProb (DTEX tm ::$ as))
