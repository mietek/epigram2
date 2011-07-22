
\section{$\eta$ Quotation}

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

> etaQuote :: Int -> (EXP :>: EXP) -> VAL
> etaQuote l (t :>: e) = etaQuoten {Z} l (ev t :>: e)

> etaQuoten :: pi (n :: Nat) . Int -> (VAL :>: EXP) -> Tm {Body, Val, n}
> etaQuoten {n} l (PI s t :>: f) = 
>   L ENil nom (exp (etaQuoten {S n} l (ev (t $$. x) :>: f $$. x)))
>   where x :: EXP 
>         x = P (l + mkInt n, nom, exp s) :$ B0
>         nom = fortran "x" [ev f, ev t] undefined 
> etaQuoten {n} l (SIGMA s t :>: p) = 
>   PAIR (exp (etaQuoten {n} l (ev s :>: p $$ Hd))) 
>        (exp (etaQuoten {n} l (ev (t $$. (p $$ Hd)) :>: p $$ Tl)))
> etaQuoten {n} l (ONE :>: _) = ZERO
> -- [Feature = Prop]
> etaQuoten {n} l (PRF _P :>: p) = CHKD (exp (etaQuotePrf {n} l (ev _P :>: p)))
> -- [/Feature = Prf]
> etaQuoten {n} l (t :>: e) = etaQuotev {n} l (t :>: ev e)

> etaQuotePrf :: pi (n :: Nat) . Int -> (VAL :>: EXP) -> Tm {Body, Val, n}
> etaQuotePrf {n} l (PI s t :>: f) = 
>   L ENil nom (exp (etaQuotePrf {S n} l (ev (t $$. x) :>: f $$. x)))
>   where x :: EXP 
>         x = P (l + mkInt n, nom, exp s) :$ B0
>         nom = fortran "x" [ev f, ev t] undefined 
> etaQuotePrf {n} l (AND _P _Q :>: p) = 
>   PAIR (exp (etaQuotePrf {n} l (ev _P :>: p $$ Hd))) 
>        (exp (etaQuotePrf {n} l (ev _Q :>: p $$ Tl)))
> etaQuotePrf {n} l (ONE :>: _) = ZERO
> etaQuotePrf {n} l (t :>: e) = etaQuotev {n} l (t :>: ev e)


> etaQuotev :: pi (n :: Nat) . Int -> (VAL :>: VAL) -> Tm {Body, Val, n}
> etaQuotev {n} l (tc :- as :>: vc :- bs) = case canTy ((tc, as) :>: vc) of
>   Nothing -> error "It will nae fit"
>   Just t  -> vc :- etaQuoteTEL {n} l (t :>: bs)

> etaQuotev {n} l (t :>: x :$ es) = 
>   let  (h :<: t) = etahQuote {n} l x  
>   in   h :$ bwdList (etaQuoteSp {n} l (x :$ B0 :<: ev t) (trail es))


> etaQuoteSp :: pi (n :: Nat) . Int -> (VAL :<: VAL) -> [Elim EXP] -> 
>                 [Elim (Tm {Body, Exp, n})]
> etaQuoteSp {n} l (e :<: t) [] = []
> etaQuoteSp {n} l (e :<: PI s t) (A a:as) = 
>   A (exp (etaQuoten {n} l (ev s :>: a))) :
>     etaQuoteSp {n} l (e $$. a :<: ev (t $$. a)) as
> etaQuoteSp {n} l (e :<: SIGMA s t) (Hd : as) =
>   Hd : etaQuoteSp {n} l (e $$ Hd :<: ev s) as
> etaQuoteSp {n} l (e :<: SIGMA s t) (Tl : as) =
>   Tl : etaQuoteSp {n} l (e $$ Tl :<: ev t $$. (e $$ Hd)) as 
> etaQuoteSp {n} l (e :<: t) (Out : as) | Just ty' <- outable t = Out : etaQuoteSp {n} l (e $$ Out :<: ev ty') as 

> etahQuote :: pi (n :: Nat) . Int -> Tm {Head, Val, Z} -> (Tm {Head, Val, n} :<: TY)
> etahQuote {n} l' (P (l, x, s)) = case levi {n} (l-l') of
>   Nothing -> P (l, x, s) :<: s
>   Just i -> (V i :<: s)
> etahQuote {n} l (Refl _S s) = 
>   Refl (exp $ etaQuoten {n} l (SET :>: _S)) (exp $ etaQuoten {n} l (ev _S :>: s)) 
>    :<: PRF (EQ _S s _S s)
> etahQuote {n} l (Coeh coeh _S _T q s) =
>     Coeh coeh (exp $ etaQuoten {n} l (SET :>: _S)) 
>               (exp $ etaQuoten {n} l (SET :>: _T))
>               (exp $ etaQuoten {n} l (PRF (EQ SET _S SET _T) :>: q))
>               (exp $ etaQuoten {n} l (ev _S :>: s)) 
>       :<: eorh coeh
>  where eorh :: Coeh -> EXP
>        eorh Coe = _S
>        eorh Coh = PRF (EQ _S s _T (Coeh Coe _S _T q s :$ B0))
> etahQuote {n} l (D def) = D def :<: defTy def 
> etahQuote {n} l x = error $ ugly V0 x    

> etaQuoteTEL :: pi (n :: Nat) . Int -> (VAL :>: [EXP]) -> [Tm {Body, Exp, n}]
> etaQuoteTEL {n} l (ONE :>: []) = []
> etaQuoteTEL {n} l (SIGMA s t :>: e : es) = 
>  exp (etaQuoten {n} l (ev s :>: e)) : etaQuoteTEL {n} l (ev (t $$. e) :>: es)
