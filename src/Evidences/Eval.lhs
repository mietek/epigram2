\section{Evaluation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.Eval where

> import Control.Applicative

> import Data.Foldable
> import Data.Maybe

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Operators

> import Features.Features ()

%endif


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

\subsection{Elimination}

The |$$| function applies an elimination principle to a value. Note
that this is open to further extension as we add new constructs and
elimination principles to the language. Extensions are added through
the |ElimComputation| aspect.

Formally, the computation rules of the featureless language are the
following:

\begin{eqnarray}
(\lambda \_ . v) u & \mapsto & v                            
    \label{eqn:Evidences.Rules.elim-cstt} \\
(\lambda x . t) v  & \mapsto & \mbox{eval } t[x \mapsto v]  
    \label{eqn:Evidences.Rules.elim-bind} \\
\mbox{unpack}(Con\ t) & \mapsto & t                         
    \label{eqn:Evidences.Rules.elim-con}  \\
(N n) \$\$ ee      & \mapsto & N (n \:\$ e)                 
    \label{eqn:Evidences.Rules.elim-stuck}
\end{eqnarray}

The rules \ref{eqn:Evidences.Rules.elim-cstt} and
\ref{eqn:Evidences.Rules.elim-bind} are standard lambda calculus
stories. Rule \ref{eqn:Evidences.Rules.elim-con} is the expected
"unpacking the packer" rule. Rule \ref{eqn:Evidences.Rules.elim-stuck}
is justified as follow: if no application rule applies, this means
that we are stuck. This can happen if and only if the application is
itself stuck. The stuckness therefore propagates to the whole
elimination.

This translates into the following code:

> ($$) :: VAL -> Elim VAL -> VAL
> L (K v)      $$ A _  = v               -- By \ref{eqn:Evidences.Rules.elim-cstt}
> L (H (vs, rho) x t)  $$ A v
>   = eval t (vs :< v, naming x v rho)   -- By \ref{eqn:Evidences.Rules.elim-bind}
> L (x :. t)   $$ A v
>   = eval t (B0 :< v, naming x v [])    -- By \ref{eqn:Evidences.Rules.elim-bind}
> C (Con t)    $$ Out  = t               -- By \ref{eqn:Evidences.Rules.elim-con}
> import <- ElimComputation              -- Extensions
> N n          $$ e    = N (n :$ e)      -- By \ref{eqn:Evidences.Rules.elim-stuck}
> f            $$ e    =  error $  "Can't eliminate\n" ++ show f ++ 
>                                  "\nwith eliminator\n" ++ show e

The |naming| operation amends the current naming scheme, taking account
the instantiation of x: see below.

The left fold of |$$| applies a value to a bunch of eliminators:

> ($$$) :: (Foldable f) => VAL -> f (Elim VAL) -> VAL
> ($$$) = Data.Foldable.foldl ($$)

\subsection{Operators}

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


\subsection{Binders}

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
> body (K v)     g            = K (eval v g)
> body (x :. t)  (B0, rho)    = txtSub rho x :. t  -- closed lambdas stay syntax
> body (x :. t)  g@(_, rho)   = H g (txtSub rho x) t

Now, as well as making closures, the current renaming scheme is applied
to the bound variable name, for cosmetic purposes.

\subsection{Evaluator}

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
> eval (L b)       = (|L (body b)|)                -- By (a)
> eval (C c)       = (|C (eval ^$ c)|)             -- By (b)
> eval (N n)       = eval n                        -- By (c)
> eval (t :? _)    = eval t                        -- By (d)
> eval (P x)       = (|(pval x)|)                  -- By (e)
> eval (V i)       = evar i                        -- By (f)
> eval (t :$ e)    = (|eval t $$ (eval ^$ e)|)     -- By (g)
> eval (op :@ vs)  = (|(op @@) (eval ^$ vs)|)      -- By (h)
> eval (Yuk v)     = (|v|)

> evar :: Int -> ENV -> VAL
> evar i (vs, ts) = fromMaybe (error "eval: bad index") (vs !. i)


Finally, the evaluation of a closed term simply consists in calling the
interpreter defined above with the empty environment.

> evTm :: Tm {d, TT} REF -> VAL
> evTm t = eval t (B0, [])


\subsection{Alpha-conversion on the fly}

Here's a bit of a dirty trick which sometimes results in better name choices.
We firstly need the notion of a textual substitution from Tm.lhs. 

< type TXTSUB = [(Char, String)]   -- renaming plan

That's a plan for mapping characters to strings. We apply them
to strings like this, with no change to characters which aren't
mapped.

> txtSub :: TXTSUB -> String -> String
> txtSub ts = foldMap blat where blat c = fromMaybe [c] $ lookup c ts

The |ENV| type packs up a renaming scheme, which we apply to every
bound variable name advice string that we encounter as we go: the
deed is done in |body|, above.

The renaming scheme is amended every time we instantiate a bound variable
with a free variable. Starting from the right, each characte of the bound
name is mapped to the corresponding character of the free name. The first
character of the bound name is mapped to the whole remaining prefix. So
instantiating |"xys"| with |"monks"| maps |'y'| to |"k"| and |'x'| to |"mon"|.
The idea is that matching the target of an eliminator in this way will
give good names to the variables bound in its methods, if we're lucky and
well prepared.

> naming :: String -> VAL -> TXTSUB -> TXTSUB
> naming x (N (P y)) rho 
>   = mkMap (reverse x) (reverse (refNameAdvice y)) rho where
>     mkMap ""        _         rho  = rho
>     mkMap _         ""        rho  = rho
>     mkMap [c]       s         rho  | s /= [c]  = (c, s) : rho
>     mkMap (c : cs)  (c' : s)  rho  | c /= c'   = mkMap cs s ((c, [c']) : rho)
>     mkMap (_ : cs)  (_ : s)   rho  = mkMap cs s rho
> naming _ _ rho = rho
