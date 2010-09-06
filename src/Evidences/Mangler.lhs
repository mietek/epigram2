\section{Variable Manipulation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

> module Evidences.Mangler where

> import Control.Applicative
> import Control.Monad.Identity

> import Kit.BwdFwd
> import Evidences.Tm

> import Kit.MissingLibrary

%endif

Variable manipulation, in all its forms, ought be handled by the
mangler. A |Mangle f x y| is a record that describes how to deal with
parameters of type |x|, variables and binders, producing terms with
parameters of type |y| and wrapping the results in some applicative
functor |f|.

It contains three fields: 
\begin{description}

\item{|mangP|} describes what to do with parameters. It takes a
parameter value and a spine (a list of eliminators) that this
parameter is applied to (handy for christening); it must produce an
appropriate term.

\item{|mangV|} describes what to do with variables. It takes a de
Brujin index and a spine as before, and must produce a term.

\item{|mangB|} describes how to update the |Mangle| in response to a
given binder name.  

\end{description}

> data Mangle f x y = Mang
>   {  mangP :: x -> f (Spine {TT} y) -> f (ExTm y)
>   ,  mangV :: Int -> f (Spine {TT} y) -> f (ExTm y)
>   ,  mangB :: String -> Mangle f x y
>   }


The interpretation of a |Mangle| is given by the |%| operator.
This mangles a term, produing a term with the
appropriate parameter type in the relevant idiom. This is basically a
traversal, but calling the appropriate fields of |Mangle| for each
parameter, variable or binder encountered.

> (%) :: Applicative f => Mangle f x y -> Tm {In, TT} x -> f (Tm {In, TT} y)
> m % L (K t)      = (|L (|K (m % t)|)|)
> m % L (x :. t)   = (|L (|(x :.) (mangB m x % t)|)|)
> m % C c          = (|C ((m %) ^$ c)|)
> m % N n          = (|N (exMang m n (|[]|))|)

The corresponding behaviour for |ExTm|s is implemented by |exMang|.

> exMang ::  Applicative f => Mangle f x y ->
>            Tm {Ex, TT} x -> f [Elim (Tm {In, TT} y)] -> f (Tm {Ex, TT} y)
> exMang m (P x)     es = mangP m x es
> exMang m (V i)     es = mangV m i es
> exMang m (o :@ a)  es = (|(| (o :@) ((m %) ^$ a) |) $:$ es|) 
> exMang m (t :$ e)  es = exMang m t (|((m %) ^$ e) : es|)
> exMang m (t :? y)  es = (|(|(m % t) :? (m % y)|) $:$ es|)


The |%%| and |%%#| operators apply mangles that use the identity functor.

> (%%) :: Mangle Identity x y -> Tm {In, TT} x -> Tm {In, TT} y
> m %% t = runIdentity $ m % t

> (%%#) :: Mangle Identity x y -> Tm {Ex, TT} x -> Tm {Ex, TT} y
> m %%# t = runIdentity $ exMang m t (| [] |)


\subsection{The |under| mangle}

The |under i y| mangle binds the variable with de Brujin index |i| to the
parameter |y| and leaves the term otherwise unchanged.

> under :: Int -> x -> Mangle Identity x x
> under i y = Mang
>   {  mangP = \ x ies -> (|(P x $:$) ies|)
>   ,  mangV = \ j ies -> (|((if i == j then P y else V j) $:$) ies|)
>   ,  mangB = \ _ -> under (i + 1) y
>   }


The |underScope| function goes under a binding, instantiating the bound variable
to the given reference.

> underScope :: Scope {TT} x -> x -> InTm x
> underScope (K t)     _ = t
> underScope (_ :. t)  x = under 0 x %% t


\subsection{The deBruijnifying mangle}

This thing takes a stack of REFs and traverses a term, turning them into
deBruijn indices (in the hope that somebody out there will $\lambda$-abstract
them). It gets used when quoting $\lambda$-abstractions in values, and when
building $\lambda$-abstractions in the proof state.

> (-||) :: Bwd REF -> INTM -> INTM
> es -|| t = disMangle es 0 %% t
>   where
>     disMangle :: Bwd REF -> Int -> Mangle Identity REF REF
>     disMangle ys i = Mang
>       {  mangP = \ x ies -> (|(h ys x i $:$) ies|)
>       ,  mangV = \ i ies -> (|(V i $:$) ies|)
>       ,  mangB = \ _ -> disMangle ys (i + 1)
>       }
>     h B0                        x i  = P x
>     h (ys :< y) x i
>       | x == y     = V i
>       | otherwise  = h ys x (i + 1)


\subsection{The substitution mangle}

The |substitute| function implements substitution for closed terms: given a list
of typed references, a corresponding list of terms and a target term, it
substitutes the terms for the references in the target.

> substitute :: Bwd (REF :<: INTM) -> Bwd INTM -> INTM -> INTM
> substitute bs vs t = substMangle bs vs %% t
>   where
>     substMangle :: Bwd (REF :<: INTM) -> Bwd INTM -> Mangle Identity REF REF
>     substMangle bs vs = Mang
>       {  mangP = \ x ies -> (|(help bs vs x $:$) ies|)
>       ,  mangV = \ i ies -> (|(V i $:$) ies|)
>       ,  mangB = \ _ -> substMangle bs vs
>       }
>     
>     help :: Bwd (REF :<: INTM) -> Bwd INTM -> REF -> EXTM
>     help B0 B0 x = P x
>     help (bs :< (y :<: ty)) (vs :< v) x
>       | x == y     = v ?? ty
>       | otherwise  = help bs vs x


\subsection{The |inc| mangle}

The |inc| mangle increments the bound variables in the term, allowing a binding
to be inserted for the call term. It keeps track of how many local binders it
has gone under, so as to not increment them.

> inc :: Int -> Mangle Identity x x
> inc n = Mang
>     {  mangP = \x ies -> (|(P x $:$) ies|)
>     ,  mangV = \j ies -> (|(V (if j >= n then j+1 else j) $:$) ies|)
>     ,  mangB = \_ -> inc (n+1)
>     }