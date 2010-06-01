\section{Rules}
\label{sec:rules}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.Rules where

> import Debug.Trace

> import Control.Applicative
> import Control.Monad.Error

> import Data.Foldable
> import Data.Traversable
> import Data.Maybe

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Mangler

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import {-# SOURCE #-} Compiler.OpDef

> import Features.Features ()

%endif

%format <-> = "\leftrightarrow"

\subsection{Computation}

In this section, we implement an interpreter for Epigram. As one would
expect, it will become handy during type-checking. We assume that
evaluated terms have been type-checked beforehand, that is: the
interpreter always terminates.

The interpreter is decomposed in four sections. First, the application
of eliminators, implemented by |$$|. Second, the execution of
operators, implemented by |@@|. Third, reduction under binder,
implemented by |body|. Finally, full term evaluation, implemented by
|eval|. At the end, this is all wrapped inside |evTm|, which evaluate
a given term in an empty environment.

\subsubsection{Elimination}

The |$$| function applies an elimination principle to a value. Note
that this is open to further extension as we add new constructs and
elimination principles to the language. Extensions are added through
the |ElimComputation| aspect.

Formally, the computation rules of the featureless language are the
following:

\begin{eqnarray}
(\lambda \_ . v) u & \mapsto & v                            \label{eqn:elim_cstt} \\
(\lambda x . t) v  & \mapsto & \mbox{eval } t[x \mapsto v]  \label{eqn:elim_bind} \\
\mbox{unpack}(Con\ t) & \mapsto & t                         \label{eqn:elim_con}  \\
(N n) \$\$ ee      & \mapsto & N (n \:\$ e)                 \label{eqn:elim_stuck}
\end{eqnarray}

The rules \ref{eqn:elim_cstt} and \ref{eqn:elim_bind} are standard
lambda calculus stories. Rule \ref{eqn:elim_con} is the expected
"unpacking the packer" rule. Rule \ref{eqn:elim_stuck} is justified as
follow: if no application rule applies, this means that we are
stuck. This can happen if and only if the application is itself
stuck. The stuckness therefore propagates to the whole elimination.

This translates into the following code:

> ($$) :: VAL -> Elim VAL -> VAL
> L (K v)      $$ A _  = v                 -- By \ref{eqn:elim_cstt}
> L (H g _ t)  $$ A v  = eval t (g :< v)   -- By \ref{eqn:elim_bind}
> L (HF _ f)   $$ A v  = f v               -- By \ref{eqn:elim_bind}
> L (x :. t)   $$ A v  = eval t (B0 :< v)  -- By \ref{eqn:elim_bind}
> C (Con t)    $$ Out  = t                 -- By \ref{eqn:elim_con}
> import <- ElimComputation                -- Extensions
> N n          $$ e    = N (n :$ e)        -- By \ref{eqn:elim_stuck}
> f            $$ e    = error ("Can't eliminate\n" ++ show f ++ "\nwith eliminator\n" ++ show e)


The left fold of |$$| applies a value to a bunch of eliminators:

> ($$$) :: (Foldable f) => VAL -> f (Elim VAL) -> VAL
> ($$$) = Data.Foldable.foldl ($$)

\subsubsection{Operators}

Running an operator is quite simple, as operators come with the
mechanics to run them. However, we are not ensured to get a value out
of an applied operator: the operator might get stuck by a neutral
argument. In such case, the operator will blame the argument by
returning it on the |Left|. Otherwise, it returns the computed value
on the |Right|.

Hence, the implementation of |@@| is as follow. First, run the
operator. On the left, the operator is stuck, so return the neutral
term consisting of the operation applied to its arguments. On the
right, we have gone down to a value, so we simply return it.

> (@@) :: Op -> [VAL] -> VAL
> op @@ vs = either (\_ -> N (op :@ vs)) id (opRun op vs) 

Note that we respect the invariant on |N| values: we have an |:@|
that, for sure, is applying at least one stuck term to an operator
that uses it.


\subsubsection{Binders}

Evaluation under binders needs to distinguish two cases:
\begin{itemize}
\item the binder ignores its argument, or
\item a variable |x| is defined and bound in a term |t|
\end{itemize}

In the first case, we can trivially go under the binder and innocently
evaluate. In the second case, we turn the binding -- a term -- into a
closure -- a value. The body grabs the current environment, extends it
with the awaited argument, and evaluate the whole term down to a
value.

This naturally leads to the following code:

> body :: Scope {TT} REF -> ENV -> Scope {VV} REF
> body (K v)     g   = K (eval v g)
> body (x :. t)  B0  = x :. t  -- closed lambdas stay syntax
> body (x :. t)  g   = H g x t
> --body (x :. t)  g   = HF x (\v -> eval t (g :< v))

\conor{I'm in the process of restoring first-order closures.}

\subsubsection{Evaluator}

Putting the above pieces together, plus some machinery, we are finally
able to implement an evaluator. On a technical note, we are working in
the Applicative |-> ENV| and use She's notation for writing
applicatives.

The evaluator is typed as follow: provided with a term and a variable
binding environment, it reduces the term to a value. The
implementation is simply a matter of pattern-matching and doing the
right thing. Hence, we evaluate under lambdas by calling |body|
(a). We reduce canonical term by evaluating under the constructor
(b). We drop off bidirectional annotations from Ex to In, just
reducing the inner term |n| (c). Similarly for type ascriptions, we
ignore the type and just evaluate the term (d). 

If we reach a parameter, either it is already defined or it is still
not binded. In both case, |pval| is the right tool: if the parameter is
intrinsically associated to a value, we grab that value. Otherwise, we
get the neutral term consisting of the stuck parameter (e).

A bound variable simply requires to extract the corresponding value
from the environment (f). Elimination is handled by |$$| defined above
(g). And similarly for operators with |@@| (h).

> eval :: Tm {d, TT} REF -> ENV -> VAL
> eval (L b)       = (|L (body b)|)                                -- By (a)
> eval (C c)       = (|C (eval ^$ c)|)                             -- By (b)
> eval (N n)       = eval n                                        -- By (c)
> eval (t :? _)    = eval t                                        -- By (d)
> eval (P x)       = (|(pval x)|)                                  -- By (e)
> eval (V i)       = fromMaybe (error "eval: bad index") . (!. i)  -- By (f)
> eval (t :$ e)    = (|eval t $$ (eval ^$ e)|)                     -- By (g)
> eval (op :@ vs)  = (|(op @@) (eval ^$ vs)|)                      -- By (h)


Finally, the evaluation of a closed term simply consists in calling the
interpreter defined above with the empty environment.

> evTm :: Tm {d, TT} REF -> VAL
> evTm t = eval t B0


\subsection{Type-checking Canonicals and Eliminators}



\subsubsection{Canonical objects}
\label{sec:canTy}


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
> import <- CanTyRules
> canTy  chev (ty :>: x)  = throwError'  $ err "canTy: the proposed value "
>                                        ++ errCan x
>                                        ++ err " is not of type " 
>                                        ++ errTyVal ((C ty) :<: SET)


\subsubsection{Eliminators}
\label{sec:elimTy}

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
> import <- ElimTyRules
> elimTy _  (v :<: t) e = throwError'  $ err "elimTy: failed to eliminate" 
>                                      ++ errTyVal (v :<: (C t)) 
>                                      ++ err "with" 
>                                      ++ errElim e

\question{Why not asking |m| to be |Alternative| too?}


> spineTy :: MonadError (StackError t) m =>
>            (TY :>: t -> m (s :=>: VAL)) -> 
>            TY -> Bwd t ->
>            m (Bwd (s :=>: VAL),TY)
> spineTy chev ty B0 = return (B0, ty) 
> spineTy chev ty (sp :< x) = do
>   (spv,PI s t) <- spineTy chev ty sp
>   xxv@(_ :=>: xv) <- chev (s :>: x)
>   return (spv :< xxv,t $$ A xv)

\subsection{Equality and Quotation}

Testing for equality is a direct application of normalization by
evaluation\cite{dybjer:nbe, chapman:phd, dybjer:dependent_types_work}:
to compare two values, we first bring them to their normal form. Then,
it is a simple matter of syntactic equality, as defined in Section
\ref{sec:syntactic_equality}, to compare the normal forms.

> equal :: (TY :>: (VAL,VAL)) -> NameSupply -> Bool
> equal (ty :>: (v1,v2)) r = quote (ty :>: v1) r == quote (ty :>: v2) r


|quote| is a type-directed operation that returns a normal form |INTM|
by recursively evaluating the value |VAL| of type |TY|. 

> quote :: (TY :>: VAL) -> NameSupply -> INTM

The normal form corresponds to a $\beta$-normal $\eta$-long form:
there are no $\beta$-redexes present and all possible
$\eta$-expansions have been performed.

This is achieved by two mutually recursive functions, |inQuote| and
|exQuote|:

< inQuote :: (TY :>: VAL) -> NameSupply -> INTM
< exQuote :: NEU -> NameSupply -> (EXTM :<: TY)

Where |inQuote| quotes values and |exQuote| quotes neutral terms. As
we are initially provided with a value, we quote it with |inQuote|, in
a fresh namespace.

> quote vty r = inQuote vty (freshNSpace r "quote")


\subsubsection{inQuote}

Quoting a value consists in, if possible, $\eta$-expanding
it. So it goes:

> inQuote :: (TY :>: VAL) -> NameSupply -> INTM
> inQuote (C ty :>: v)          r | Just t    <- etaExpand (ty :>: v) r = t

Needless to say, we can always $\eta$-expand a closure. Therefore, if
$\eta$-expansion has failed, there are two possible cases: either we
are quoting a neutral term, or a canonical term. In the case of
neutral term, we switch to |exQuote|, which is designed to
quote neutral terms.

However, we are allowed to |simplify| the neutral term before handling
it to |exQuote|. Simplification is discussed in greater length
below. To give an intuition, it consists in transforming stuck terms
into equivalent, yet simpler, stuck terms. Typically, we use this
opportunity to turn some laws (monad law, functor law, etc.) to hold
\emph{definitionally}. This is known as Boutillier's
trick~\cite{boutillier:report}.

> inQuote (_ :>: N n)      r = N t
>     where (t :<: _) = exQuote (simplify n r) r

In the case of a canonical term, we use |canTy| to check that |cv| is
of type |cty| and, more importantly, to evaluate |cty|. Then, it is
simply a matter of quoting this |typ :>: val| inside the canonical
constructor, and returning the fully quoted term. The reason for the
presence of |Just| is that |canTy| asks for a |MonadError|. Obviously,
we cannot fail in this code, but we have to be artificially cautious.

> inQuote (C cty :>: C cv) r = either 
>     (error $ 
>         "inQuote: impossible! Type " ++ show (fmap (\_ -> ()) cty) ++ 
>         " doesn't admit " ++ show cv)
>     id $ do
>          ct <- canTy chev (cty :>: cv)
>          return $ C $ fmap termOf ct
>              where chev (t :>: v) = do
>                    let tv = inQuote (t :>: v) r
>                    return $ tv :=>: v
>
> inQuote (C x :>: t) r = error $ 
>     "inQuote: type " ++ show (fmap (\_ -> ()) x) ++ 
>     " doesn't admit " ++ show t


\subsubsection{$\eta$-expansion}

As mentioned above, |\eta|-expansion is the first sensible thing to do
when quoting. Sometimes it works, especially for closures and features
for which a |CanEtaExpand| aspect is defined. Quoting a closure is a bit
tricky: you cannot compute under a binder as you would like to. So, we
first have to generate a fresh variable |v|. Then, we apply |v| to the
function |f|, getting a value of type |t v|. At this point, we can
safely quote the term. The result is a binding of |v| in the quoted
term.

> etaExpand :: (Can VAL :>: VAL) -> NameSupply -> Maybe INTM
> etaExpand (Pi s t :>: f) r = Just $
>   L ("__etaExpandA" :.
>      fresh ("__etaExpandB" :<: s) 
>      (\v  -> inQuote (t $$ A v :>: (f $$ A v))) r)
> import <- CanEtaExpand
> etaExpand _                  _ = Nothing



\subsubsection{exQuote}

Now, let us examine the quotation of neutral terms. Remember that a
neutral term is either a parameter, a stuck elimination, or a stuck
operation. Hence, we consider each cases in turn.

> exQuote :: NEU -> NameSupply -> (EXTM :<: TY)

To quote a free variable, ie. a parameter, the idea is the
following. If we are asked to quote a free variable |P|, there are two
possible cases. First case, we have introduced it during an
$\eta$-expansion (see |etaExpand|, above). Hence, we know that it is
bound by a lambda: it needs to be turned into the bound variable |V|,
with the right De Bruijn index. Second case, we have not introduced
it: we can simply return it as such.

> exQuote (P x)       r = quop x r :<: pty x
>     where quop :: REF -> NameSupply -> EXTM
>           quop ref@(ns := _) r = help (bwdList ns) r
>               where
>               help (ns :< (_,i)) (r,j) = if ns == r then V (j-i-1) else P ref

\begin{danger}

The code above relies on the very structure of the names, as provided
by the |NameSupply|. We know that a free variable has been created by
|quote| if and only if the current name supply and the namespace |ns|
of the variable are the same. Hence, the test |ns == r|. Then, we
compute the De Bruijn index of the bound variable by counting the
number of lambdas traversed up to now -- by looking at |j-1| in our
current name supply |(r,j)| -- minus the number of lambdas traversed
at the time of the parameter creation, ie. |i|. Do some math, pray,
and you get the right De Bruijn index.

\end{danger}

If an elimination is stuck, it is because the function is stuck while
the arguments are ready to go. So, we have to recursively |exQuote|
the neutral application, while |inQuote|-ing the arguments. 

> exQuote (n :$ v)    r = (n' :$ e') :<: ty'
>     where (n' :<: ty)  = exQuote n r
>           e' = fmap termOf e
>           Right (e,ty') = elimTy chev (N n :<: unC ty) v
>           chev (t :>: x) = do
>             let tx = inQuote (t :>: x) r
>             return $ tx :=>: x
>           unC :: VAL -> Can VAL
>           unC (C ty) = ty


Similarly, if an operation is stuck, this means that one of the value
passed as an argument needs to be |inQuote|-ed. So it goes. Note that
the operation itself cannot be stuck: it is a simple fully-applied
constructor which can always compute.

> exQuote (op :@ vs)  r = (op :@ vals) :<: v 
>     where (vs',v) = either  (error "exQuote: impossible happened.")
>                             id $ opTy op chev vs 
>           vals = map termOf vs'
>           chev (t :>: x) = do
>               let tx = inQuote (t :>: x) r
>               return $ tx :=>: x


\subsubsection{bquote}

As we are in the quotation business, let us define $\beta$-quotation,
ie. |bquote|. Unlike |quote|, |bquote| does not perform
$\eta$-expansion, it just brings the term in $\beta$-normal
form. Therefore, the code is much more simpler than |quote|, although
the idea is the same.

\begin{danger}

It is important to note that we are in a |NameSupplier| and we don't
require a specially crafted |NameSupply| (unlike |quote| and |quop|,
as described above). Because of that, we have to maintain the
variables we have generated and to which De Bruijn index they
correspond. This is the role of the backward list of references. Note
also that we let the user provide an initial environment of
references: this is useful to discharge a bunch of assumptions inside
a term. The typical use-case is |discharge|, below.

\end{danger}

Apart from that, this is a standard $\beta$-quotation: 

> bquote :: NameSupplier m => Bwd REF -> Tm {d,VV} REF -> m (Tm {d,TT} REF)

If binded by one of our lambda, we bind the free variables to the
right lambda. We don't do anything otherwise.

> bquote  refs (P x) =
>     case x `elemIndex` refs of
>       Just i -> pure $ V i 
>       Nothing -> pure $ P x

Constant lambdas are painlessly structural.

> bquote refs (L (K t))   = (| LK (bquote refs t) |)

When we see a syntactic lambda value, we are very happy, because
quotation is just renaming.

> -- bquote refs (L (x :. t)) = (| (refs -|| L (x :. t)) |)

For all other lambdas, it's the usual story: we create a fresh variable,
evaluate the applied term, quote the result, and bring everyone under
a binder.

> bquote refs f@(L _) = 
>     (|(L . (x :.))
>       (freshRef  (x :<: error "bquote: type undefined") 
>                  (\x -> bquote  (refs :< x) 
>                                 (f $$ A (pval x))))|)
>     where x = fortran f

For the other constructors, we simply go through and do as much damage
as we can. Simple, easy.

> bquote refs (C c)       = (| C (traverse (bquote refs) c) |)
> bquote refs (N n)       = (| N (bquote refs n) |)
> bquote refs (n :$ v)    = (| (bquote refs n) :$ (traverse (bquote refs) v) |)
> bquote refs (op :@ vs)  = (| (op :@) (traverse (bquote refs) vs) |)

\subsubsection{discharge}

Given a value, we might want to discharge an hypothesis used deep down
in it. That is, provided a free variable |ref|, we have to track it
inside |val| and, when found, bind it to the De Bruijn index 0. This
corresponds to beta-quoting |val| with |ref|. Then, well, we put that
under a lambda and we are discharged.

> discharge :: NameSupplier m => REF -> VAL -> m VAL
> discharge ref val = (| (evTm . L . (fst (last (refName ref)) :.)) (bquote (B0 :< ref) val) |)


\subsection{Simplification of stuck terms}

\question{Got to write something about that. Me tired. Another time.}

> simplify :: NEU -> NameSupply -> NEU
> simplify n r = exSimp n r
>
> inSimp :: VAL -> NameSupply -> VAL
> inSimp (N n) = (| N (exSimp n) |)
> inSimp v     = (| v |)
>
> exSimp :: NEU -> NameSupply -> NEU
> exSimp (P x)      = (| (P x) |)
> exSimp (n :$ el)  = (| exSimp n :$ (inSimp ^$ el) |)
> exSimp (op :@ vs) = opS op <*> (inSimp ^$ vs)
>   where
>     opS op r vs = case opSimp op vs r of
>       Nothing -> op :@ vs
>       Just n  -> n

\subsection{Type checking}
\label{subsec:type-checking}

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
Section~\ref{sec:check_monad}.

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

> import <- Check
> check (ty :>: tm) = throwError'  $ err "check: type mismatch: type"
>                                  ++ errTyVal (ty :<: SET)
>                                  ++ err "does not admit"
>                                  ++ errTm tm


\subsection{Type inference}
\label{subsec:type-inference}

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



\subsection{Operators and primitives}
\label{subsec:operators}

In this section, we weave some She aspects. In particular, we bring
inside @Rules.lhs@ the |operators| defined by feature files,
along with any auxiliary code.

> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

> import <- OpCode
> import <- RulesCode

The list of |primitives| includes axioms and fundamental definitions provided 
by the |Primitives| aspect, plus a reference corresponding to each operator.

> primitives :: [(String, REF)]
> primitives = map (\op -> (opName op, mkRef op)) operators ++ (
>     import <- Primitives
>     [])
>   where
>     mkRef :: Op -> REF
>     mkRef op = [("Operators",0),(opName op,0)] := (DEFN opEta :<: opTy)
>       where
>         opTy = pity $ opTyTel op
>
>         opEta = opEtaTac (opArity op) []
>
>         opEtaTac :: Int -> [VAL] -> VAL
>         opEtaTac 0 args = op @@ (reverse args) 
>         opEtaTac n args = L $ HF "mkRef" $ \l -> opEtaTac (n-1) (l : args) 

We can look up the primitive reference corresponding to an operator using
|lookupOpRef|. This ensures we maintain sharing of these references.

> lookupOpRef :: Op -> REF
> lookupOpRef op = case lookup (opName op) primitives of
>     Just ref  -> ref
>     Nothing   -> error $ "lookupOpRef: missing operator primitive " ++ show op



\subsection{Observational Equality}

Let's have some observational equality, now!
\cite{altenkirch_mcbride_swierstra:obs_equality}

\question{Can we move this to the appropriate feature file?
Does nested use of import aspects work?}


The |eqGreen| operator, defined in section~\ref{sec:features_equality},
computes the proposition that two values are equal if their containing
sets are equal. We write |<->| for application of this operator.

> (<->) :: (TY :>: VAL) -> (TY :>: VAL) -> VAL
> (y0 :>: t0) <-> (y1 :>: t1) = eqGreen @@ [y0,t0,y1,t1]


We define the computational behaviour of the |eqGreen| operator as follows,

> opRunEqGreen :: [VAL] -> Either NEU VAL

> import <- OpRunEqGreen

> opRunEqGreen [C (Pi sS1 tT1), f1, C (Pi sS2 tT2), f2] = Right $ 
>   ALL sS1 . L . HF "s1" $  \ s1 -> ALL sS2 . L . HF "s2" $ \ s2 ->
>   IMP  (EQBLUE (sS1 :>: s1) (sS2 :>: s2)) $
>   (tT1 $$ A s1 :>: f1 $$ A s1) <-> (tT2 $$ A s2 :>: f2 $$ A s2)

> opRunEqGreen [SET, PI sS1 tT1, SET, PI sS2 tT2] = Right $
>    AND  ((SET :>: sS2) <-> (SET :>: sS1))
>         (ALL sS2 . L . HF "s2" $ \ s2 -> ALL sS1 . L . HF "s1" $  \ s1 ->
>            IMP  (EQBLUE (sS2 :>: s2) (sS1 :>: s1)) $
>            (SET :>: tT1 $$ A s1) <-> (SET :>: tT2 $$ A s2))

> opRunEqGreen [SET, C (Mu (_ :?=: Id t0)), SET, C (Mu (_ :?=: Id t1))] = 
>     opRunEqGreen [desc, t0, desc, t1]

Unless overridden by a feature or preceding case, we determine equality
of canonical values in canonical sets by labelling subterms of the values
with their types, half-zipping them together (ensuring that the head
constructors are identical) and requiring that the subterms are equal.

> opRunEqGreen [C ty0, C t0, C ty1, C t1] =
>     case halfZip (fmap termOf t0') (fmap termOf t1') of
>         Nothing  -> Right ABSURD 
>         Just x   -> Right $ mkEqConj (trail x)
>   where
>     Right t0'  = canTy (\tx@(t :>: x) -> Right (tx :=>: x)) (ty0 :>: t0)
>     Right t1'  = canTy (\tx@(t :>: x) -> Right (tx :=>: x)) (ty1 :>: t1)

If one of the arguments is neutral, we blame it for being unable to compute.

> opRunEqGreen [C _,   N t0,  C _,   _     ] = Left t0
> opRunEqGreen [C _,   _,     C _,   N t1  ] = Left t1
> opRunEqGreen [N y0,  _,     _,     _     ] = Left y0 
> opRunEqGreen [_,     _,     N y1,  _     ] = Left y1


The |mkEqConj| function builds a conjunction of |eqGreen| propositions
by folding over a list. It is uniformly structural for canonical
terms, ignoring contravariance. Therefore, this requires a special
case for |Pi| in |opRunEqGreen|.

> mkEqConj :: [(TY :>: VAL,TY :>: VAL)] -> VAL
> mkEqConj ((tt0, tt1) : [])  = tt0 <-> tt1
> mkEqConj ((tt0, tt1) : xs)  = AND (tt0 <-> tt1) (mkEqConj xs)
> mkEqConj []                 = TRIVIAL


The |coeh| function takes two types, a proof that they are equal and a value
in the first type; it produces a value in the second type and a proof that
it is equal to the original value. If the sets are definitinoally equal then
this is easy, otherwise it applies |coe| to the value and uses the coherence
axiom |coh| to produce the proof.

> coeh :: TY -> TY -> VAL -> VAL -> (VAL, VAL)
> coeh s t q v | partialEq s t q  = (v, pval refl $$ A s $$ A v)
> coeh s t q v = (coe @@ [s, t, q, v], pval coh $$ A s $$ A t $$ A q $$ A v)


The |coerce| function transports values between equal canonical sets. Given two
sets built from the same canonical constructor (represented as |Can (VAL, VAL)|,
a proof of their equality and an element of the first set, it will try to return
|Right v| where |v| is an element of the second set. If computation is blocked
by a neutral value |n|, it will return |Left n|.

Features must extend this definition using the |Coerce| aspect for every
canonical set-former they introduce. They must handle coercions between all
canonical inhabitants of such sets, but need not deal with neutral inhabitants.
To ensure we can add arbitrary consistent axioms to the system, they should
not inspect the proof, but may eliminate it with |naughtE| if asked to coerce
between incompatible sets.

> coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
> coerce Set q x = Right x
> coerce (Pi (sS1, sS2) (tT1, tT2)) q f1 = Right . L . HF (fortran tT2) $ \ s2 ->
>   let  (s1, sq) = coeh sS2 sS1 (CON $ q $$ Fst) s2
>        t1 = f1 $$ A s1
>   in   coe @@ [tT1 $$ A s1, tT2 $$ A s2,
>                  CON $ q $$ Snd $$ A s2 $$ A s1 $$ A sq, t1]
> import <- Coerce
> coerce _    q  (N x)  = Left x
> coerce cvv  q  r      = error $ unlines ["coerce: can't cope with sets",
>                             show cvv, "and proof", show q, "and value", show r]


The |partialEq| function takes two sets together with a proof that they are
equal; it returns |True| if they are known to be definitionally equal. This
is sound but not complete for the definitional equality, so if it returns
|False| they might still be equal. It is safe to call during bquote, and
hence during evaluation, because it avoids forcing the types of references.


> partialEq :: VAL -> VAL -> VAL -> Bool
> partialEq _ _ (N (P r :$ _ :$ _)) | r == refl = True
> partialEq _ _ _ = False

Sadly we cannot do the following, because it is not safe to invent a name supply.

< partialEq s t _ = bquote B0 s ns == bquote B0 t ns
<   where ns = (B0 :< ("__partialEq", 0), 0) :: NameSupply