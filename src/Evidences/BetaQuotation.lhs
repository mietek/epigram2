\section{$\beta$-Quotation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.BetaQuotation where

> import Control.Applicative

> import Data.Traversable

> import Kit.BwdFwd

> import Evidences.Tm
> import Evidences.Eval

> import NameSupply.NameSupplier

> import Features.Features ()

%endif


As we are in the quotation business, let us define $\beta$-quotation,
ie. |bquote|. Unlike |quote|, |bquote| does not perform
$\eta$-expansion, it just brings the term in $\beta$-normal
form. Therefore, the code is much more simpler than |quote|, although
the idea is the same.

\begin{danger}

It is important to note that we are in a |NameSupplier| and we don't
require a specially crafted |NameSupply| (unlike |quote| and
|quop|). Because of that, we have to maintain the variables we have
generated and to which De Bruijn index they correspond. This is the
role of the backward list of references. Note also that we let the
user provide an initial environment of references: this is useful to
discharge a bunch of assumptions inside a term.

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

\pierre{This is part of Conor's experiment on Term
representations. The following line could be de-commented and that
would be ok. However, this does not compute as much as the next case,
hence the current Cochon user has to see things he doesn't want to
see. This could be solved by some Distillation work but we prefer to
avoid over-engineering Cochon's Distillation for the time being.}

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

