\section{Equality and Quotation}
\label{sec:Evidences.DefinitionalEquality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.DefinitionalEquality where

> import Control.Applicative

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Eval
> import Evidences.TypeChecker

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Features.Features ()

%endif

Testing for equality is a direct application of normalization by
evaluation\cite{dybjer:nbe, chapman:phd, dybjer:dependent_types_work}:
to compare two values, we first bring them to their normal form. Then,
it is a simple matter of syntactic equality, as defined in Section
\ref{subsec:Evidences.Tm.syntactic-equality}, to compare the normal
forms.

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


\subsection{inQuote}

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
> inQuote (x :>: t) r = error $ 
>     "inQuote: type " ++ show x ++ " doesn't admit " ++ show t


\subsection{$\eta$-expansion}

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



\subsection{exQuote}

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

