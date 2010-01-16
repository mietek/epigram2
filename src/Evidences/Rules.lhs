\section{Rules}
\label{sec:rules}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.Rules where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import Data.Foldable
> import Data.Traversable
> import Data.Maybe

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Features.Features


> import {-# SOURCE #-} Evidences.Tactics

%endif


\subsection{Computation}

In this section, we implement an interpreter for Epigram. As one would
expect, it will become handy during type-checking. We assume that
evaluated terms have been type-checked beforehand, that is: the
interpreter always terminates.

The interpreter is decomposed in four blocks. First, the application
of eliminators, implemented by |$$|. Second, the execution of
operators, implemented by |@@|. Third, reduction under binder,
implemented by |body|. Finally, full term evaluation, implemented by
|eval|. At the end, this is all wrapped inside |evTm|, to evaluate a
given term in an empty environment.

\subsubsection{Elimination}

The |$$| function applies an elimination principle to a value. Note
that it is open to further extension as we add new constructs and
elimination principles to the language. Extensions are added through
the |ElimComputation| aspect.

Formally, the computation rules of the Core language are the
following:

\begin{eqnarray}
(\lambda \_ . v) u & \mapsto & v                            \label{eqn:elim_cstt} \\
(\lambda x . t) v  & \mapsto & \mbox{eval } t[x \mapsto v]  \label{eqn:elim_bind} \\
\mbox{unpack}(Con\ t) & \mapsto & t                         \label{eqn:elim_con}  \\
(N n) \$\$ ee      & \mapsto & N (n \:\$ e)                 \label{eqn:elim_stuck}
\end{eqnarray}

The rules \ref{eqn:elim_cstt} and \ref{eqn:elim_bind} are standard
lambda calculus stories. Rule \ref{eqn:elim_stuck} is justified as
follow: if no application rule applies, this means that we are
stuck. This can happen if and only if the application is itself
stuck. The stuckness therefore propagates to the whole elimination.

\question{What is the story for |Con| and |out|?}

This translates into the following code:

> ($$) :: VAL -> Elim VAL -> VAL
> L (K v)      $$ A _  = v                -- By \ref{eqn:elim_cstt}

< L (H g _ t)  $$ A v  = eval t (g :< v)  -- By \ref{eqn:elim_bind}

> L (HF _ f)   $$ A v  = f v
> C (Con t)    $$ Out  = t                -- By \ref{eqn:elim_con}
> import <- ElimComputation               -- Extensions
> N n          $$ e    = N (n :$ e)       -- By \ref{eqn:elim_stuck}
> f            $$ e    = error ("Can't eliminate\n" ++ show f ++ "\nwith eliminator\n" ++ show e)


\subsubsection{Operators}

Running an operator is quite simple, as operators come with the
mechanics to be ran, through |opRun|. However, we are not ensured to
get a value out of an applied operator: the operator might get stuck
by a neutral argument. In such case, the operator will blame the
argument by returning it on the |Left|. Otherwise, it returns the
computed value on the |Right|. 

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
closure -- a value. The closure environment will be the current
evaluation environment, whereas the name and the binded terms remain
the same.

This naturally leads to the following code:

> body :: Scope {TT} REF -> ENV -> Scope {VV} REF
> body (K v)     g = K (eval v g)
> body (x :. t)  g = HF x (\v -> eval t (g :< v)) -- H g x t

\subsubsection{Evaluator}

Putting the above pieces together, plus some machinery, we are finally
able to implement an evaluator. 

On a technical note, we are working in the Applicative |-> ENV| and
use She's notation for writing applicatives.

The evaluator is typed as follow: provided with a term and a variable
binding environment, it reduces the term to a value.

> eval :: Tm {d, TT} REF -> ENV -> VAL

The implementation is simply a matter of pattern-matching and doing
the right thing. Hence, we evaluate under lambdas by calling |body|:

> eval (L b)       = (|L (body b)|)

We reduce canonical term by evaluating under the constructor:

> eval (C c)       = (|C (eval ^$ c)|)

We drop off bidirectional annotations from Ex to In, just reducing the
inner term |n|:

\question{Any other subtlety here?}

> eval (N n)       = eval n

Similarly for type ascriptions, we ignore the type and just evaluate
the term:

> eval (t :? _)    = eval t


If we reach a parameter, either it is already defined or it is still
not binded. In both case, |pval| is the right tool: if the parameter is
intrinsically associated to a value, we grab that value. Otherwise, we
get the neutral term consisting of the stuck parameter.

> eval (P x)       = (|(pval x)|)

A bound variable simply requires to extract the corresponding value
from the environment:

> eval (V i)       = (!. i)

Elimination is handled by |$$| defined above:

> eval (t :$ e)    = (|eval t $$ (eval ^$ e)|)

And similarly for operators with |@@|:

> eval (op :@ vs)  = (|(op @@) (eval ^$ vs)|)

Anything else is probably display syntax that we should not encounter:

> eval x           = error ("eval: cannot evaluate " ++ show x)


\subsubsection{Putting things together}

Finally, the evaluation of a closed term simply consists in calling the
interpreter defined above with the empty environment.

> evTm :: Tm {d, TT} REF -> VAL
> evTm t = eval t B0


\subsection{Type-checking Canonicals and Eliminators}

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

However, in order to implement tactics, we have to generalize this
function. The generalization consists in parameterizing |canTy| with a
type-directed function |TY :>: t -> s|, which is equivalent to 
|TY -> t -> s|. Because we are still using the concept of evaluation, both
functions are fused into a single one, of type: |TY :>: t -> (s,VAL)|.
To support the use of tactics, which can fail to produce a
value, we extend this type to |TY :>: t -> m (s,VAL)| where |m| is a
|MonadError|.

Hence, by defining an appropriate function |chev|, we can recover the
previous definition of |canTy|. We can also do much more: intuitively,
we can write any type-directed function in term of |canTy|. That is,
any function traversing the types derivation tree can be expressed
using |canTy|.

> canTy ::  (Alternative m, MonadError [String] m) =>
>           (TY :>: t -> m (s :=>: VAL)) -> (Can VAL :>: Can t) -> m (Can (s :=>: VAL))
> canTy chev (Set :>: Set)     = return Set
> canTy chev (Set :>: Pi s t)  = do
>   ssv@(s :=>: sv) <- chev (SET :>: s)
>   ttv@(t :=>: tv) <- chev (ARR sv SET :>: t)
>   return $ Pi ssv ttv
> import <- CanTyRules
> canTy  chev (ty :>: x)  = throwError' $ "canTy: the proposed value "
>                                      ++ show (fmap (\x -> ".") x)
>                                      ++ " is not of type " ++ show ty


Type-checking elimination forms mirrors |canTy|. |elimTy| is provided
with a checker-evaluator, a value |f| of inferred typed |t|, ie. a |f
:<: t| of |VAL :<: Can VAL|, and an eliminator of |Elim t|. If the
operation is type-safe, we are given back the eliminator enclosing the
result of |chev| and the type of the eliminated value.

it computes the type of the argument,
ie. the eliminator, in |Elim (s :=>: VAL)| and the type of the result in
|TY|.

> elimTy :: MonadError [String] m => (TY :>: t -> m (s :=>: VAL)) -> 
>           (VAL :<: Can VAL) -> Elim t ->
>           m (Elim (s :=>: VAL),TY)
> elimTy chev (f :<: Pi s t) (A e) = do
>   eev@(e :=>: ev) <- chev (s :>: e)
>   return $ (A eev, t $$ A ev) 
> import <- ElimTyRules
> elimTy _  (v :<: t) e = throwError' $ "elimTy: failed to eliminate " ++ show v ++ 
>                                    " with " ++ (show $ fmap (\t -> ".") e)


\subsection{Equality and Quotation}

Testing for equality is a direct application of normalization by
evaluation\cite{dybjer:nbe, chapman:phd, dybjer:dependent_types_work}:
to compare two values, we first bring them to their normal form. Then,
it is a simple matter of syntactic equality, defined in Section
\ref{sec:syntactic_equality}, to compare the normal forms.

> equal :: (TY :>: (VAL,VAL)) -> NameSupply -> Bool
> equal (ty :>: (v1,v2)) r = quote (ty :>: v1) r == quote (ty :>: v2) r


|quote| is a type-directed operation that returns a normal form |INTM|
by recursively evaluating the value |VAL| of type |TY|. The normal
form corresponds to a $\beta$-normal $\eta$-long form: there are no
$\beta$-redexes present and all possible $\eta$-expansions have been
performed.

\question{Is that right? It's $\beta$-$\eta$-stuff?}

This is performed by two mutually recursive functions, |inQuote| and
|exQuote|:

< inQuote :: (TY :>: VAL) -> NameSupply -> INTM
< exQuote :: NEU -> NameSupply -> (EXTM :<: TY)

Where |inQuote| quotes values and |exQuote| quotes neutral terms. As
we are initially provided with a value, we quote it with |inQuote|, in
a fresh namespace.

> quote :: (TY :>: VAL) -> NameSupply -> INTM
> quote vty r = inQuote vty (freshNSpace r "quote")


Quoting a value consists in, if possible, $\eta$-expanding
it. So it goes:

> inQuote :: (TY :>: VAL) -> NameSupply -> INTM
> inQuote (C ty :>: v)          r | Just t    <- etaExpand (ty :>: v) r = t

Needless to say, we can always $\eta$-expand a closure. Therefore, if
$\eta$-expansion has failed, there are two possible cases: either we
are quoting a neutral term, or a canonical term. In the case of
neutral term, we simply switch to |exQuote|, which is designed to
quote neutral terms:

> inQuote (_ :>: N n)      r = N t
>     where (t :<: _) = exQuote (simplify n r) r

In the case of a canonical term, we use |canTy| to check that |cv| is
of type |cty| and, more importantly, to evaluate |cty|. Then, it is
simply a matter of quoting this |type :>: val| inside the canonical
constructor, and returning the fully quoted term. The reason for the
breeding of |Just| is that we are in the |Maybe| monad, and we really
want to stay in there: |canTy| asks for a |MonadError|. Obviously, we
cannot fail in this code, but we have to be artificially
cautious. Hence, this is |Just| a mess.

> inQuote (C cty :>: C cv) r = fromJust $ do
>     ct <- canTy chev (cty :>: cv)
>     return $ C $ fmap termOf ct
>         where chev (t :>: v) = do
>                 let tv = inQuote (t :>: v) r
>                 return $ tv :=>: v
>
> inQuote (C x :>: t) r = error $ 
>     "inQuote: type " ++ show (fmap (\_ -> ()) x) ++ 
>     " doesn't admit " ++ show t

As mentioned above, |\eta|-expansion is the first sensible thing to do
when quoting. Sometimes it works, especially for closures and features
for which an |EtaExpand| aspect is defined. Quoting a closure is a bit
tricky: you cannot compute under a binder as you would like to. So, we
first have to generate a fresh variable |v|. Then, we apply |v| to the
function |f|, getting a value of type |t v|. At this point, we can
safely quote this term. The result is a binding of |v| in the quoted
term.

> etaExpand :: (Can VAL :>: VAL) -> NameSupply -> Maybe INTM
> etaExpand (Pi s t :>: f) r = Just $
>   L ("__etaExpandA" :.
>      fresh ("__etaExpandB" :<: s) 
>      (\v  -> inQuote (t $$ A v :>: (f $$ A v))) r)
> import <- EtaExpand
> etaExpand _                  _ = Nothing


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

Let's be clear. The code above is, in my opinion, a hack.
Technically, we know that a free variable has been created by |quote|
if and only if the current name supply and the namespace |ns| of the
variable are the same. Hence, the test |ns == r|. Then, we compute the
De Bruijn index of the bound variable by counting the number of
lambdas traversed up to now -- by looking at |j-1| in our current name
supply |(r,j)| -- minus the number of lambdas traversed at the time of
the parameter creation, ie. |i|. Do some math, pray, and you get the
right De Bruijn index.


If an elimination is stuck, it is because the function is stuck while
the arguments are ready to go. So, we have to recursively |exQuote|
the neutral application, while |inQuote|-ing the arguments. 

> exQuote (n :$ v)    r = (n' :$ e') :<: ty'
>     where (n' :<: ty)  = exQuote n r
>           e' = fmap termOf e
>           Just (e,ty') = elimTy chev (N n :<: unC ty) v
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
>     where (vs',v) = fromJust $ opTy op chev vs 
>           vals = map termOf vs'
>           chev (t :>: x) = do
>               let tx = inQuote (t :>: x) r
>               return $ tx :=>: x


As we are in the quotation business, let us define $\beta$-quotation,
ie. |bquote|. Unlike |quote|, |bquote| does not perform
$\eta$-expansion, but just brings the term in $\beta$-normal
form. Therefore, the code is much more simpler than |quote|, although
the idea is the same.

From a technical point of view, it is important to note that we are in
a |NameSupplier| and we don't require a specially crafted |NameSupply|
(unlike |quote| and |quop|, as described above). Because of that, we
have to maintain the variables we have generated and to which De
Bruijn index they correspond. This is the role of the backward list of
references. Note also that we let the user provide an initial
environment of references: this is useful to discharge a bunch of
assumptions inside a term. The typical use-case is |discharge| in
@Tactics.lhs@.

Apart from that, this is a standard $\beta$-quotation: 

> bquote :: NameSupplier m => Bwd REF -> Tm {d,VV} REF -> m (Tm {d,TT} REF)

If binded by one of our lambda, we bind the free variables to the
(hopefully) correct lambda. We don't do anything otherwise.

> bquote  refs (P x) =
>     case x `elemIndex` refs of
>       Just i -> pure $ V i 
>       Nothing -> pure $ P x

Going under a closure is the usual story: we create a fresh variable,
evaluate the applied term, quote the result, and bring everyone under
a binder.

> bquote refs (L (HF x t)) = 
>     (|(\t -> L (x :. t))
>       (NameSupply.NameSupplier.freshRef (x :<: undefined) 
>                       (\x -> bquote (refs :< x) 
>                                     (t (pval x))))|)

For the other constructors, we simply go through and do as much damage
as we can. Simple, easy.

> bquote refs (L (K t)) = (|(L . K) (bquote refs t) |)
> bquote refs (C c) = (|C (traverse (bquote refs) c )|)
> bquote refs (N n) = (|N (bquote refs n )|)
> bquote refs (n :$ v) = (|(:$) (bquote refs n)
>                                 (traverse (bquote refs) v)|)
> bquote refs (op :@ vs) = (|(:@) (pure op)
>                                   (traverse (bquote refs) vs)|)

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

Technically, we also need a name supply and handle failure with the |Maybe|
monad:

> check :: (TY :>: INTM) -> Check (() :=>: VAL)

Type-checking a canonical term is rather easy, as we just have to
delegate the hard work to |canTy|. The checker-evaluator simply needs
to evaluate the well-typed terms.

> check (C c :>: C c')         = do
>   cc' <- canTy chev (c :>: c')
>   return $ () :=>: (C $ fmap valueOf cc')
>     where chev (t :>: x) = do 
>               ch <- check (t :>: x)  
>               return $ ch :=>: evTm x

As for lambda, we know it is simple too. We wish the code was simple
too. But, hey, it isn't. The formal typing rule is the following:

\begin{prooftree}
\AxiomC{$x : S \vdash T x \ni t$}
\UnaryInfC{$\Pi S\ T \ni \lambda x . t$}
\end{prooftree}

As for the implementation, we apply the by-now standard trick of
making a fresh variable $x \in S$ and computing the type |T x|. Then,
we simply have to check that $T\ x \ni t$.

> check (PI s t :>: L sc) = do
>   NameSupply.NameSupplier.freshRef ("__check" :<: s) 
>            (\ref -> check (t $$ A (pval ref) :>: underScope sc ref)) 
>   return $ () :=>: (evTm $ L sc)

Formally, we can bring the |Ex| terms into the |In| world with the
rule:

\begin{prooftree}
\AxiomC{$n \in Y$}
\AxiomC{$\star \ni W \equiv Y$}
\BinaryInfC{$W \ni n$}
\end{prooftree}

This translates naturally into the following code:

> check (w :>: N n)            = do
>   r <- askNSupply
>   yv :<: yt <- infer n
>   guard $ equal (SET :>: (w, yt)) r
>   return $ () :=>: yv

Finally, we can extend the checker with the |Check| aspect. If no rule
has matched, then we have to give up.

> import <- Check
> check _                     = throwError' "check: type mismatch"


\subsection{Type inference}
\label{subsec:type-inference}

On the inference side, we also have a valid typing environment
$\Gamma$ that is used to pull types |TY| out of |Ex| terms:

$$\Gamma \vdash \mbox{Tm \{Ex,.\} p} \in \mbox{TY}$$

This translates into the following signature:

> infer :: EXTM -> Check (VAL :<: TY)

We all know the rule to infer the type of a free variable from the
context:

\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma, x : A, \Delta \vdash x \in A$}
\end{prooftree}

In Epigram, parameters carry there types, so it even easier:

> infer (P x)               = return $ pval x :<: pty x

The rule for eliminators is a generalization of the rule for function
application. Let us give a look at its formal rule:

\begin{prooftree}
\AxiomC{$f \in \Pi\ S\ T$}
\AxiomC{$S \ni x$}
\BinaryInfC{$f x \in {(B x)}^\downarrow$}
\end{prooftree}

The story is the same in the general case: we infer the eliminated
term |t| and we type-check the eliminator, using |elimTy|. Because
|elimTy| computes the result type, we have inferred the result type.

> infer (t :$ s)           = do
>   val :<: C ty <- infer t
>   (s',ty') <- elimTy chev (evTm t :<: ty) s
>   return $ (val $$ (fmap valueOf s')) :<: ty'
>       where chev (t :>: x) = do 
>               ch <- check (t :>: x) 
>               return $ ch :=>: evTm x

Following exactly the same principle, we can infer the result of an
operator application:

> infer (op :@ ts)         = do
>   (vs,t) <- opTy op chev ts
>   return $ (op @@ (fmap valueOf vs)) :<: t
>       where chev (t :>: x) = do 
>               ch <- check (t :>: x) 
>               return $ ch :=>: evTm x

Type ascription is formalized by the following rule:

\begin{prooftree}
\AxiomC{$\star \ni \mbox{ty}$}
\AxiomC{$\mbox{ty}^\downarrow \ni t$}
\BinaryInfC{$(t :\in T) \in \mbox{ty}^\downarrow$}
\end{prooftree}

Which translates directly into the following code:

> infer (t :? ty)           = do
>   check (SET :>: ty)
>   let vty = evTm ty
>   () :=>: v <- check (vty :>: t)
>   return $ v :<: vty

Obviously, if none of the rule above applies, then there is something
fishy.

> infer _                   = throwError' "infer: unable to infer type"


\subsection{Operators}

In this section, we weave some She aspects. In particular, we bring
inside @Rules.lhs@ the |OpCode|s and |Operators| defined in the
various Features.

> import <- OpCode
>
> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

> import <- AxCode
>
> axioms :: [(String, REF)]
> axioms = (
>   import <- Axioms
>   [])

> primitives :: [(String, REF)]
> primitives = (
>   import <- Primitives
>   [])


We also define and import some handy tactics, sugaring some canonical
constructors to make them easier to swallow.

> setTac :: Tac VAL
> setTac = can Set

> conTac :: Tac VAL -> Tac VAL
> conTac t = can $ Con t

> piTac :: Tac VAL -> (REF -> Tac VAL) -> Tac VAL
> piTac s t = can $ Pi s (lambda t)

> arrTac :: Tac VAL -> Tac VAL -> Tac VAL
> arrTac s t = piTac s (\_ -> t)

> (@@@) :: REF -> [Tac VAL] -> Tac VAL
> f @@@ xs = foldl' app (use f) xs $ done
>     where app f x = f . apply (A x)

> var :: REF -> Tac VAL
> var r = use r done

> import <- SugarTactics


> mkRef :: Op -> REF
> mkRef op = [("Operators",0),(opName op,0)] := (DEFN opEta :<: opTy)
>     where opTy = pity $ opTyTel op
>           opEta = opEtaTac (opArity op) []
>           opEtaTac :: Int -> [VAL] -> VAL
>           opEtaTac 0 args = op @@ (reverse args) 
>           opEtaTac n args = L $ HF "mkRef" $ \l -> opEtaTac (n-1) (l : args) 


> import -> Primitives where
>     (map (\op -> (opName op, mkRef op)) 
>          operators) ++


\subsection{Definitions from feature files}

> import <- BootstrapDesc
> import <- QuotientDefinitions

\subsection{Observational Equality}

\question{|mkEqConj| does not respect contravariance in the |Pi| rule,
          and, in general, does not introduce quantifiers. At first
          glance, this contradicts the definition in the OTT paper.}

That's true: this presentation is uniformly structural for canonical
terms, ignoring contravariance. It will work out the same in the end,
provided we remember to apply symmetry when we use the proofs in
contravariant positions. It seemed cheap at the time, but perhaps it's
a false economy.


> mkEqConj :: [(TY :>: VAL,TY :>: VAL)] -> VAL
> mkEqConj ((y0 :>: t0,y1 :>: t1) : []) = eqGreen @@ [y0,t0,y1,t1]
> mkEqConj ((y0 :>: t0,y1 :>: t1) : xs) = 
>   AND (eqGreen @@ [y0,t0,y1,t1]) (mkEqConj xs)
> mkEqConj []                           = TRIVIAL

> (<->) :: (TY :>: VAL) -> (TY :>: VAL) -> VAL
> (y0 :>: t0) <-> (y1 :>: t1) = eqGreen @@ [y0,t0,y1,t1]


> opRunEqGreen :: [VAL] -> Either NEU VAL
> import <- OpRunEqGreen
> opRunEqGreen [C (Pi sS1 tT1),f1,C (Pi sS2 tT2),f2] = Right $ 
>   ALL sS1 . L . HF "s1" $  \ s1 -> ALL sS2 . L . HF "s2" $ \ s2 ->
>   IMP  (EQBLUE (sS1 :>: s1) (sS2 :>: s2)) $
>   (tT1 $$ A s1 :>: f1 $$ A s1) <-> (tT2 $$ A s2 :>: f2 $$ A s2)
> opRunEqGreen [SET, PI sS1 tT1, SET, PI sS2 tT2] = Right $
>    AND  ((SET :>: sS2) <-> (SET :>: sS1))
>         (ALL sS2 . L . HF "s2" $ \ s2 -> ALL sS1 . L . HF "s1" $  \ s1 ->
>            IMP  (EQBLUE (sS2 :>: s2) (sS1 :>: s1)) $
>            (SET :>: tT1 $$ A s1) <-> (SET :>: tT2 $$ A s2))
> opRunEqGreen [C ty0,C t0,C ty1,C t1] = case halfZip t0'' t1'' of
>    Nothing -> Right ABSURD 
>    Just x  -> Right $ mkEqConj (trail x)
>    where
>    Just t0' = canTy (\tx@(t :>: x) -> Just (tx :=>: x)) (ty0 :>: t0)
>    t0'' = fmap (\(x :=>: y) -> x) t0'
>    Just t1' = canTy (\tx@(t :>: x) -> Just (tx :=>: x)) (ty1 :>: t1)
>    t1'' = fmap (\(x :=>: y) -> x) t1'
> opRunEqGreen [C _,N t0,C _,_] = Left t0
> opRunEqGreen [C _,_,C _,N t1] = Left t1
> opRunEqGreen [N y0,_,_,_] = Left y0 
> opRunEqGreen [_,_,N y1,_] = Left y1 
> opRunEqGreen [C y0,_,C y1,_] = Right TRIVIAL



> coeh :: TY -> TY -> VAL -> VAL -> (VAL, VAL)
> coeh s t (N (P r :$ _ :$ _)) v | r == refl = (v, pval refl $$ A s $$ A v)
> coeh s t q v = (coe @@ [s, t, q, v], pval coh $$ A s $$ A t $$ A q $$ A v)

> coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
> coerce Set q x = Right x
> coerce (Pi (sS1,sS2) (tT1,tT2)) q f1 = Right . L . HF (fortran tT2) $ \ s2 ->
>   let  (s1, sq) = coeh sS2 sS1 (q $$ Fst) s2
>        t1 = f1 $$ A s1
>   in   coe @@ [tT1 $$ A s1, tT2 $$ A s2, q $$ Snd $$ A s2 $$ A s1 $$ A sq]
> import <- Coerce
> coerce _ q (N x) = Left x



