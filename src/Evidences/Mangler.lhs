\section{Variable Manipulation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

> module Evidences.Mangler where

> import Control.Applicative
> import Control.Monad.Identity

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


The |%%| operator applies a mangle that uses the identity functor.

> (%%) :: Mangle Identity x y -> Tm {In, TT} x -> Tm {In, TT} y
> m %% t = runIdentity $ m % t



\subsection{The Under mangler}

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
