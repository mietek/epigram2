
\section{\eta Quotation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}

> module Evidences.EtaQuote where

> import Prelude hiding (foldl, exp)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import qualified Data.Monoid as M
> import Data.Foldable
> import Data.List hiding (foldl)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Evidences.Tm
> import Evidences.TypeCheckRules

%endif

> levi :: pi (n :: Nat) . Int -> Maybe (Fin {n})
> levi {n} l = bound {n} (mkInt n - l - 1)

> etaQuote :: (EXP :>: EXP) -> VAL
> etaQuote (t :>: e) = etaQuoten {Z} (ev t :>: e)

> etaQuoten :: pi (n :: Nat) . (VAL :>: EXP) -> Tm {Body, Val, n}
> etaQuoten {l} (PI s t :>: f) = 
>   L ENil nom (exp (etaQuoten {S l} (ev (t $$. x) :>: f $$. x)))
>   where x :: EXP 
>         x = P (mkInt l, nom, exp s) :$ B0
>         nom = fortran "x" [ev f, ev t] undefined 
> etaQuoten {l} (SIGMA s t :>: p) = 
>   PAIR (exp (etaQuoten {l} (ev s :>: p $$ Hd))) 
>        (exp (etaQuoten {l} (ev (t $$. (p $$ Hd)) :>: p $$ Tl)))
> etaQuoten {l} (ONE :>: _) = ZERO
> -- [Feature = Prop]
> etaQuoten {l} (PRF _ :>: _) = CHKD
> -- [Feature = Prf]
> etaQuoten {l} (t :>: e) = etaQuotev {l} (t :>: ev e)

> etaQuotev :: pi (n :: Nat) . (VAL :>: VAL) -> Tm {Body, Val, n}
> etaQuotev {l} (tc :- as :>: vc :- bs) = case canTy ((tc, as) :>: vc) of
>   Nothing -> error "It will nae fit"
>   Just t  -> vc :- etaQuoteTEL {l} (t :>: bs)

> etaQuotev {l} (t :>: x :$ es) = 
>   let  (h :<: t) = etahQuote {l} x  
>   in   h :$ bwdList (etaQuoteSp {l} (x :$ B0 :<: ev t) (trail es))
> etaQuotev {l} (x :>: D def ss op) = D def ss op 


> etaQuoteSp :: pi (n :: Nat) . (VAL :<: VAL) -> [Elim EXP] -> 
>                 [Elim (Tm {Body, Exp, n})]
> etaQuoteSp {n} (e :<: t) [] = []
> etaQuoteSp {n} (e :<: PI s t) (A a:as) = 
>   A (exp (etaQuoten {n} (ev s :>: a))) :
>     etaQuoteSp {n} (e $$. a :<: ev (t $$. a)) as
> etaQuoteSp {n} (e :<: SIGMA s t) (Hd : as) =
>   Hd : etaQuoteSp {n} (e $$ Hd :<: ev s) as
> etaQuoteSp {n} (e :<: SIGMA s t) (Tl : as) =
>   Tl : etaQuoteSp {n} (e $$ Tl :<: ev t $$. (e $$ Hd)) as 

> {-
> etaQuotev {l} (t :>: x :$ es) = 
>   let  (h :<: t) = etahQuote {l} x  
>   in   h :$ fstEx (etaQuoteSp {l} (h :<: ev t) es) 

> etaQuoteSp :: pi (n :: Nat) . (Tm {Head, Val, n} :<: VAL) -> 
>                Bwd (Tm {Body, Exp, Z}) -> (Bwd (Tm {Body, Exp, n}) :<: VAL)
> etaQuoteSp {n} (h :<: t) B0 = (B0 :<: t)
> etaQuoteSp {n} ht@(h :<: t) (es :< e) = case (etaQuoteSp {n} ht es, e) of
>   (vs :<: PI s t, _) -> 
>     (vs :< exp (etaQuoten {n} (ev s :>: e))) :<: ev (t $$ e) 
>   (vs :<: SIGMA s t, Hd) -> (vs :< Hd :<: ev s) 
>   (vs :<: SIGMA s t, Tl) -> (vs :< Tl) :<: undefined  

<     t :: Tm {Body, Exp, Z}, h :: Tm {Head, Val, n} 
 
<     (vs :< Tl :<: wk t :$ (B0 :< (exp h :$ (vs :< Hd)))) 

> -}

> etahQuote :: pi (n :: Nat) . Tm {Head, Val, Z} -> (Tm {Head, Val, n} :<: TY)
> etahQuote {n} (P (l, x, s)) = case levi {n} l of
>   Nothing -> error "Dutch level overflow"
>   Just i -> (V i :<: s)
> etahQuote {n} (Refl _S s) = 
>   Refl (exp $ etaQuoten {n} (SET :>: _S)) (exp $ etaQuoten {n} (ev _S :>: s)) 
>    :<: PRF (EQ _S s _S s)
> etahQuote {n} (Coeh coeh _S _T q s) =
>     Coeh coeh (exp $ etaQuoten {n} (SET :>: _S)) 
>               (exp $ etaQuoten {n} (SET :>: _T))
>               (exp $ etaQuoten {n} (PRF (EQ SET _S SET _T) :>: q))
>               (exp $ etaQuoten {n} (ev _S :>: s)) 
>       :<: eorh coeh
>  where eorh :: Coeh -> EXP
>        eorh Coe = _S
>        eorh Coh = PRF (EQ _S s _T (Coeh Coe _S _T q s :$ B0))
> etahQuote {n} (D def ss op) = D def ss op 
>       :<: (defTy def $$$. (bwdList (rewindStk ss [])))
> etahQuote {n} x = error $ ugly V0 x    

> etaQuoteTEL :: pi (n :: Nat) . (VAL :>: [EXP]) -> [Tm {Body, Exp, n}]
> etaQuoteTEL {l} (ONE :>: []) = []
> etaQuoteTEL {l} (SIGMA s t :>: e : es) = 
>  exp (etaQuoten {l} (ev s :>: e)) : etaQuoteTEL {l} (ev (t $$. e) :>: es)
