\section{Type-checker}
\label{sec:Evidences.TypeChecker}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.TypeChecker where

> import Control.Applicative
> import Control.Monad.Error

> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Eval
> import {-# SOURCE #-} Evidences.DefinitionalEquality
> import Evidences.Operators

> import NameSupply.NameSupplier

%endif


\subsection{Type-checking Canonicals and Eliminators}

\subsubsection{Canonical objects}
\label{subsubsec:Evidences.TypeChecker.canTy}


Historically, canonical terms were type-checked by the following
function:

< canTy :: (t -> VAL) -> (Can VAL :>: Can t) -> Maybe (Can (TY :>: t))
< canTy ev (Set :>: Set)    = Just Set
< canTy ev (Set :>: Pi s t) = Just (Pi (SET :>: s) ((ARR (ev s) SET) :>: t)
< canTy _  _            = Nothing

If we temporally forget Features, we have here a type-checker that
takes an evaluation function |ev|, a type, and a term to be checked
against this type. When successful, the result of typing is a
canonical term that contains both the initial term and its normalized
form, as we get it for free during type-checking.

However, to avoid re-implementing the typing rules in various places,
we had to generalize this function. The generalization consists in
parameterizing |canTy| with a type-directed function |TY :>: t -> s|,
which is equivalent to |TY -> t -> s|. Because we still need an
evaluation function, both functions are fused into a single one, of
type: |TY :>: t -> (s,VAL)|.  To support failures, we extend this type
to |TY :>: t -> m (s,VAL)| where |m| is a |MonadError|.

Hence, by defining an appropriate function |chev|, we can recover the
previous definition of |canTy|. We can also do much more: intuitively,
we can write any type-directed function in term of |canTy|. That is,
any function traversing the types derivation tree can be expressed
using |canTy|.

> canTy ::  (Alternative m, MonadError (StackError t) m) =>
>           (TY :>: t -> m (s :=>: VAL)) -> 
>           (Can VAL :>: Can t) ->
>           m (Can (s :=>: VAL))
> canTy chev (Set :>: Set)     = return Set
> canTy chev (Set :>: Pi s t)  = do
>   ssv@(s :=>: sv) <- chev (SET :>: s)
>   ttv@(t :=>: tv) <- chev (ARR sv SET :>: t)
>   return $ Pi ssv ttv
> -- import <- CanTyRules
> -- [Feature = Anchor]
> canTy chev (Set :>: Anchors) = return Anchors
> canTy chev (Anchors :>: Anchor u t ts) = do
>     uuv <- chev (UID :>: u)
>     ttv@(t :=>: tv) <- chev (SET :>: t)
>     tstsv <- chev (ALLOWEDBY tv :>: ts)
>     return $ Anchor uuv ttv tstsv
> canTy chev (Set :>: AllowedBy t) = do
>     ttv <- chev (SET :>: t)
>     return $ AllowedBy ttv
> canTy chev (AllowedBy t :>: AllowedEpsilon) = do
>     return $ AllowedEpsilon
> canTy chev (AllowedBy ty :>: AllowedCons _S _T q s ts) = do
>     _SSv@(_S :=>: _Sv) <- chev (SET :>: _S)
>     _TTv@(_T :=>: _Tv) <- chev (ARR _Sv SET :>: _T)
>     qqv <- chev (PRF (EQBLUE (SET :>: ty) (SET :>: PI _Sv _Tv)) :>: q)
>     ssv@(s :=>: sv) <- chev (_Sv :>: s)
>     tstsv <- chev (ALLOWEDBY (_Tv $$ (A sv)) :>: ts)
>     return $ AllowedCons _SSv _TTv qqv ssv tstsv
> -- [/Feature = Anchor]
> -- [Feature = Enum]
> canTy chev (Set :>: EnumT e)  = do
>   eev@(e :=>: ev) <- chev (enumU :>: e)
>   return $ EnumT eev
> canTy _ (EnumT (CON e) :>: Ze)       | CONSN <- e $$ Fst  = return Ze 
> canTy chev (EnumT (CON e) :>: Su n)  | CONSN <- e $$ Fst  = do
>   nnv@(n :=>: nv) <- chev (ENUMT (e $$ Snd $$ Snd $$ Fst) :>: n)
>   return $ Su nnv
> -- [/Feature = Enum]
> -- [Feature = Equality]
> canTy chev (Prop :>: EqBlue (y0 :>: t0) (y1 :>: t1)) = do
>   y0y0v@(y0 :=>: y0v) <- chev (SET :>: y0)
>   t0t0v@(t0 :=>: t0v) <- chev (y0v :>: t0)
>   y1y1v@(y1 :=>: y1v) <- chev (SET :>: y1)
>   t1t1v@(t1 :=>: t1v) <- chev (y1v :>: t1)
>   return $ EqBlue (y0y0v :>: t0t0v) (y1y1v :>: t1t1v)
> canTy chev (Prf (EQBLUE (y0 :>: t0) (y1 :>: t1)) :>: Con p) = do
>   ppv@(p :=>: pv) <- chev (PRF (eqGreen @@ [y0, t0, y1, t1]) :>: p)
>   return $ Con ppv
> -- [/Feature = Equality]
> -- [Feature = IDesc]
> canTy chev (Set :>: IMu (ml :?=: (Id ii :& Id x)) i)  = do
>   iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>   mlv <- traverse (chev . (ARR iiv ANCHORS :>:)) ml
>   xxv@(x :=>: xv) <- chev (ARR iiv (idesc $$ A iiv) :>: x)
>   iiv <- chev (iiv :>: i)
>   return $ IMu (mlv :?=: (Id iiiiv :& Id xxv)) iiv
> canTy chev (IMu tt@(_ :?=: (Id ii :& Id x)) i :>: Con y) = do
>   yyv <- chev (idescOp @@ [ ii
>                           , x $$ A i 
>                           , L $ "i" :. [.i. 
>                               C (IMu (fmap (-$ []) tt) (NV i)) ]
>                           ] :>: y)
>   return $ Con yyv
> -- [/Feature = IDesc]
> -- [Feature = Labelled]
> canTy chev (Set :>: Label l t) = do
>    ttv@(t :=>: tv) <- chev (SET :>: t)
>    llv@(l :=>: lv) <- chev (tv :>: l)
>    return (Label llv ttv)
> canTy chev (Label l ty :>: LRet t) = do
>    ttv@(t :=>: tv) <- chev (ty :>: t)
>    return (LRet ttv)
> -- [/Feature = Labelled]
> -- [Feature = Problem]
> canTy chev (Set :>: Prob) = return Prob
> canTy chev (Prob :>: ProbLabel u s a) = do
>   uuv <- chev (UID :>: u)
>   ssv@(_ :=>: sv) <- chev (SCH :>: s)
>   aav <- chev (argsOp @@ [sv] :>: a)
>   return $ ProbLabel uuv ssv aav
> canTy chev (Prob :>: PatPi u s p) = do
>   uuv <- chev (UID :>: u)
>   ssv <- chev (SET :>: s)
>   ppv <- chev (PROB :>: p)
>   return $ PatPi uuv ssv ppv

> canTy chev (Set :>: Sch) = return Sch
> canTy chev (Sch :>: SchTy s) = do
>   ssv <- chev (SET :>: s)
>   return $ SchTy ssv
> canTy chev (Sch :>: SchExpPi s t) = do
>   ssv@(_ :=>: sv) <- chev (SCH :>: s)
>   ttv <- chev (ARR (schTypeOp @@ [sv]) SCH :>: t)
>   return $ SchExpPi ssv ttv
> canTy chev (Sch :>: SchImpPi s t) = do
>   ssv@(_ :=>: sv) <- chev (SET :>: s)
>   ttv <- chev (ARR sv SCH :>: t)
>   return $ SchImpPi ssv ttv
> -- [/Feature = Problem]
> -- [Feature = Prop]
> canTy _   (Set :>: Prop) = return Prop
> canTy chev  (Set :>: Prf p) = (|Prf (chev (PROP :>: p))|)
> canTy chev  (Prop :>: All s p) = do
>   ssv@(_ :=>: sv) <- chev (SET :>: s)
>   ppv <- chev (ARR sv PROP :>: p)
>   return $ All ssv ppv
> canTy chev  (Prop :>: And p q) = 
>   (|And (chev (PROP :>: p)) (chev (PROP :>: q))|)
> canTy _  (Prop :>: Trivial) = return Trivial
> canTy _   (Prop :>: Absurd) = return Absurd
> canTy chev  (Prf p :>: Box (Irr x)) = (|(Box . Irr) (chev (PRF p :>: x))|)
> canTy chev (Prf (AND p q) :>: Pair x y) = do
>   (|Pair (chev (PRF p :>: x)) (chev (PRF q :>: y))|)
> canTy _   (Prf TRIVIAL :>: Void) = return Void
> canTy chev (Prop :>: Inh ty) = (|Inh (chev (SET :>: ty))|)
> canTy chev (Prf (INH ty) :>: Wit t) = (|Wit (chev (ty :>: t))|)
> -- [/Feature = Prop]
> -- [Feature = Sigma]
> canTy _   (Set :>: Unit) = return Unit
> canTy chev  (Set :>: Sigma s t) = do
>   ssv@(s :=>: sv) <- chev (SET :>: s)
>   ttv@(t :=>: tv) <- chev (ARR sv SET :>: t)
>   return $ Sigma ssv ttv
> canTy _   (Unit :>: Void) = return Void
> canTy chev  (Sigma s t :>: Pair x y) =  do
>   xxv@(x :=>: xv) <- chev (s :>: x)
>   yyv@(y :=>: yv) <- chev ((t $$ A xv) :>: y)
>   return $ Pair xxv yyv
> -- [/Feature = Sigma]
> -- [Feature = UId]
> canTy _  (Set :>: UId)    = return UId
> canTy _  (UId :>: Tag s)  = return (Tag s)
> -- [/Feature = UId]
> canTy  chev (ty :>: x)  = throwError'  $ err "canTy: the proposed value "
>                                        ++ errCan x
>                                        ++ err " is not of type " 
>                                        ++ errTyVal ((C ty) :<: SET)


\subsubsection{Eliminators}
\label{subsubsec:Evidences.TypeChecker.elimTy}

Type-checking eliminators mirrors |canTy|. |elimTy| is provided with a
checker-evaluator, a value |f| of inferred typed |t|, ie. a |f :<: t|
of |VAL :<: Can VAL|, and an eliminator of |Elim t|. If the operation
is type-safe, we are given back the eliminator enclosing the result of
|chev| and the type of the eliminated value.

it computes the type of the argument,
ie. the eliminator, in |Elim (s :=>: VAL)| and the type of the result in
|TY|.

> elimTy ::  MonadError (StackError t) m =>
>            (TY :>: t -> m (s :=>: VAL)) -> 
>            (VAL :<: Can VAL) -> Elim t ->
>            m (Elim (s :=>: VAL),TY)
> elimTy chev (f :<: Pi s t) (A e) = do
>   eev@(e :=>: ev) <- chev (s :>: e)
>   return $ (A eev, t $$ A ev) 
> -- import <- ElimTyRules
> -- [Feature = Equality]
> elimTy chev (_ :<: Prf (EQBLUE (t0 :>: x0) (t1 :>: x1))) Out =
>   return (Out, PRF (eqGreen @@ [t0 , x0 , t1 , x1]))
> -- [/Feature = Equality]
> -- [Feature = IDesc]
> elimTy chev (_ :<: (IMu tt@(_ :?=: (Id ii :& Id x)) i)) Out = 
>   return (Out, 
>     idescOp @@ [  ii , x $$ A i 
>                ,  L $ "i" :. [.i. C (IMu (fmap (-$ []) tt) (NV i)) ] ])
> -- [/Feature = IDesc]
> -- [Feature = Labelled]
> elimTy chev (_ :<: Label _ t) (Call l) = do
>    llv@(l :=>: lv) <- chev (t :>: l)
>    return (Call llv, t)
> -- [/Feature = Labelled]
> -- [Feature = Prop]
> elimTy chev (f :<: Prf (ALL p q))      (A e)  = do
>   eev@(e :=>: ev) <- chev (p :>: e)
>   return $ (A eev, PRF (q $$ A ev))
> elimTy chev (_ :<: Prf (AND p q))      Fst    = return (Fst, PRF p)
> elimTy chev (_ :<: Prf (AND p q))      Snd    = return (Snd, PRF q)
> -- [/Feature = Prop]
> -- [Feature = Sigma]
> elimTy chev (_ :<: Sigma s t) Fst = return (Fst, s)
> elimTy chev (p :<: Sigma s t) Snd = return (Snd, t $$ A (p $$ Fst))
> -- [/Feature = Sigma]
> elimTy _  (v :<: t) e = throwError'  $ err "elimTy: failed to eliminate" 
>                                      ++ errTyVal (v :<: (C t)) 
>                                      ++ err "with" 
>                                      ++ errElim e

\question{Why not asking |m| to be |Alternative| too?}


\subsubsection{Operators}

The |opTy| function explains how to interpret the telescope |opTyTel|:
it labels the operator's arguments with the types they must have and
delivers the type of the whole application. To do that, one must be
able to evaluate arguments. It is vital to type-check the sub-terms
(left to right) before trusting the type at the end. This corresponds
to the following type:

< opTy :: forall t. (t -> VAL) -> [t] -> Maybe ([TY :>: t] , TY)
< opTy ev args = (...)

Where we are provided an evaluator |ev| and the list of arguments,
which length should be the arity of the operator. If the type of the
arguments is correct, we return them labelled with their type and the
type of the result.

However, we had to generalize it. Following the evolution of |canTy|
in Section~\ref{subsubsec:Evidences.TypeChecker.canTy}, we have adopted the
following scheme:

> opTy ::  (Alternative m, MonadError (StackError t) m) =>
>          Op -> (TY :>: t -> m (s :=>: VAL)) -> [t] ->
>          m ([s :=>: VAL], TY)

First, the |MonadError| constraint allows seamless integration in the
world of things that might fail. Second, we have extended the
evaluation function to perform type-checking at the same time. We also
liberalise the return type to |s|, to give more freedom in the choice
of the checker-evaluator. This change impacts on |exQuote|, |infer|,
and |useOp|. If this definition is not clear now, it should become
clear after the definition of |canTy| in
Section~\ref{subsubsec:Evidences.TypeChecker.canTy}.

> opTy op chev ss
>   | length ss == opArity op = telCheck chev (opTyTel op :>: ss)
> opTy op _ _ = throwError' $  (err "operator arity error: ")
>                              ++ (err $ opName op)


\subsection{Type checking}
\label{subsec:Evidences.TypeChecker.type-checking}

Here starts the bidirectional type-checking story. In this section, we
address the Checking side. In the next section, we implement the
Inference side. Give Conor a white-board, three pens of different
colors, 30 minutes, and you will know what is happening below in the
Edinburgh style. If you can bear with some black-and-white boring
sequents, keep reading.

The checker works as follow. In a valid typing environment $\Gamma$,
it checks that the term $t$ is indeed of type $T$, ie. $t$ can be
pushed into $T$: |T :>: t|:

$$\Gamma \vdash \mbox{TY} \ni \mbox{Tm \{In,.\} p}$$

Technically, we also need a name supply and handle failure with a
convenient monad. Therefore, we jump in the |Check| monad defined in
Section~\ref{subsec:NameSupply.NameSupplier.check-monad}.

> check :: (TY :>: INTM) -> Check INTM (INTM :=>: VAL)

Type-checking a canonical term is rather easy, as we just have to
delegate the hard work to |canTy|. The checker-evaluator simply needs
to evaluate the well-typed terms.

> check (C cty :>: C ctm) = do
>   cc' <- canTy check (cty :>: ctm)
>   return $ C ctm :=>: (C $ fmap valueOf cc')


As for lambda, it is simple too. We wish the code was simple
too. But, hey, it isn't. The formal typing rule is the following:
%
\[
\Rule{x : S \vdash T x \ni t}
     {\Pi S\ T \ni \lambda x . t}
\]

As for the implementation, we apply the by-now standard trick of
making a fresh variable $x \in S$ and computing the type |T x|. Then,
we simply have to check that $T\ x \ni t$.

> check (PI s t :>: L sc) = do
>   freshRef  ("__check" :<: s) 
>             (\ref -> check (  t $$ A (pval ref) :>: 
>                               underScope sc ref)) 
>   return $ L sc :=>: (evTm $ L sc)

Formally, we can bring the |Ex| terms into the |In| world with the
rule:
%
\[
\Rule{n \in Y  \qquad
      \star \ni W \equiv Y}
     {W \ni n}
\]

This translates naturally into the following code:

> check (w :>: N n) = do
>   r <- askNSupply
>   yv :<: yt <- infer n
>   case (equal (SET :>: (w, yt)) r) of
>     True -> return $ N n :=>: yv
>     False -> throwError'  $   err "check: inferred type"
>                           ++  errTyVal (yt :<: SET)
>                           ++  err "of"
>                           ++  errTyVal (yv :<: yt)
>                           ++  err "is not"
>                           ++  errTyVal (w :<: SET)

Finally, we can extend the checker with the |Check| aspect. If no rule
has matched, then we have to give up.

> -- import <- Check
> -- [Feature = Prop]
> check (PRF (ALL p q) :>: L sc)  = do
>   freshRef  ("" :<: p)
>             (\ref -> check (  PRF (q $$ A (pval ref)) :>: 
>                               underScope sc ref))
>   return $ L sc :=>: (evTm $ L sc)
> -- [/Feature = Prop]

> check (ty :>: tm) = throwError'  $ err "check: type mismatch: type"
>                                  ++ errTyVal (ty :<: SET)
>                                  ++ err "does not admit"
>                                  ++ errTm tm


\subsection{Type inference}
\label{subsec:Evidences.TypeChecker.type-inference}

On the inference side, we also have a valid typing environment
$\Gamma$ that is used to pull types |TY| out of |Ex| terms:

$$\Gamma \vdash \mbox{Tm \{Ex,.\} p} \in \mbox{TY}$$

This translates into the following signature:

> infer :: EXTM -> Check INTM (VAL :<: TY)

We all know the rule to infer the type of a free variable from the
context:
%
\[
\CAxiom{\Gamma, x : A, \Delta \vdash x \in A}
\]

In Epigram, parameters carry their types, so it is even easier:

> infer (P x)               = return $ pval x :<: pty x

The rule for eliminators is a generalization of the rule for function
application. Let us give a look at its formal rule:
%
\[
\Rule{f \in \Pi\ S\ T  \qquad
      S \ni x}
     {f x \in {(B x)}^\downarrow}
\]

The story is the same in the general case: we infer the eliminated
term |t| and we type-check the eliminator, using |elimTy|. Because
|elimTy| computes the result type, we have inferred the result type.

> infer (t :$ s)           = do
>     val :<: ty <- infer t
>     case ty of
>         C cty -> do
>             (s', ty') <- elimTy check (val :<: cty) s
>             return $ (val $$ (fmap valueOf s')) :<: ty'
>         _ -> throwError' $ err "infer: inferred type"
>                            ++ errTyVal (ty :<: SET)
>                            ++ err "of"
>                            ++ errTyVal (val :<: ty)
>                            ++ err "is not canonical."

Following exactly the same principle, we can infer the result of an
operator application:

> infer (op :@ ts)         = do
>   (vs,t) <- opTy op check ts
>   return $ (op @@ (fmap valueOf vs)) :<: t

Type ascription is formalized by the following rule:
%
\[
\Rule{\star \ni \mbox{ty}  \qquad
      \mbox{ty}^\downarrow \ni t}
     {(t :\in T) \in \mbox{ty}^\downarrow}
\]

Which translates directly into the following code:

> infer (t :? ty)           = do
>   _ :=>:  vty  <- check (SET  :>: ty  )
>   _ :=>:  v    <- check (vty  :>: t   )
>   return $ v :<: vty

Obviously, if none of the rule above applies, then there is something
fishy.

> infer _                   = throwError' $ err "infer: unable to infer type"





