
\section{$\eta$ Quotation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies, PatternGuards #-}

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
> import Evidences.Primitives
> import Evidences.TypeCheckRules

%endif

> levi :: pi (n :: Nat) . Int -> Maybe (Fin {n})
> levi {n} l = bound {n} (mkInt n - l - 1)

> etaQuote :: Int -> (EXP :>: EXP) -> VAL
> etaQuote l (t :>: e) = etaQuoten {Z} l (ev t :>: e)

> etaQuoten :: pi (n :: Nat) . Int -> (VAL :>: EXP) -> Tm {Body, Val, n}
> etaQuoten {n} l = etaQuoten' {n} l False

> etaQuoten' :: pi (n :: Nat) . Int -> Bool -> (VAL :>: EXP) -> Tm {Body, Val, n}
> -- [Feature = Prop]
> etaQuoten' {n} l False (PRF _P :>: p) = CHKD (exp (etaQuoten' {n} l True (PRF _P :>: p)))
> -- [/Feature = Prop]
> etaQuoten' {n} l b (ty :>: f) | Just (_, s, t) <- lambdable ty =
>   let  x :: EXP ; x = P (l + mkInt n, nom, exp s) :$ B0
>        nom = fortran "x" [ev f] undefined 
>   in   L ENil nom (exp (etaQuoten' {S n} l b (ev (t x) :>: f $$. x)))
> etaQuoten' {n} l b (ty :>: p) | Just (s, t) <- projable ty = 
>   PAIR (exp (etaQuoten' {n} l b (ev s :>: p $$ Hd))) 
>        (exp (etaQuoten' {n} l b (ev (t (p $$ Hd)) :>: p $$ Tl)))
> etaQuoten' {n} l b (ONE :>: _) = ZERO
> etaQuoten' {n} l b (t :>: e) = etaQuotev {n} l (t :>: ev e)

> etaQuotev :: pi (n :: Nat) . Int -> (VAL :>: VAL) -> Tm {Body, Val, n}
> etaQuotev {n} l (tc :- as :>: vc :- bs) = case canTy ((tc, as) :>: vc) of
>   Nothing -> error "It will nae fit"
>   Just t  -> vc :- etaQuoteTEL {n} l (t :>: bs)
> etaQuotev {n} l (B d@(SIMPLDTY na _I uDs) :$ (B0 :< A i) :>: Con :- [x]) = 
>   Con :- [ exp $  etaQuoten {n} l (ev (D idescDEF :$ (B0 
>                     :< A _I 
>                     :< A (IFSIGMA (D constrDEF :$ (B0 :< A _I :< A uDs))
>                            (D conDDEF :$ (B0 :< A _I :< A uDs :< A i)))
>                     :< A (B (SIMPLDTY na _I uDs) :$ B0))) :>: x) ]

> etaQuotev {n} l (t :>: x :$ es) = 
>   let  (h :<: t) = etahQuote {n} l x  
>   in   h :$ bwdList (etaQuoteSp {n} l (x :$ B0 :<: ev t) (trail es))
> etaQuotev {n} l (ty :>: x :- xs) = error $ show x    


> etaQuoteSp :: pi (n :: Nat) . Int -> (VAL :<: VAL) -> [Elim EXP] -> 
>                 [Elim (Tm {Body, Exp, n})]
> etaQuoteSp {n} l (e :<: t) [] = []
> etaQuoteSp {n} l (e :<: ty) (A a:as) = case lambdable ty of
>   Just (_,s,t) ->
>     A (exp (etaQuoten {n} l (ev s :>: a))) :
>       etaQuoteSp {n} l (e $$. a :<: ev (t a)) as
>   Nothing -> error "The impossible happened in etaQuoteSp (A)"
> etaQuoteSp {n} l (e :<: ty) (Hd : as) = case projable ty of
>   Just (s,t) ->
>     Hd : etaQuoteSp {n} l (e $$ Hd :<: ev s) as
>   Nothing -> error "The impossible happened in etaQuoteSp (Hd)"
> etaQuoteSp {n} l (e :<: ty) (Tl : as) = case projable ty of
>   Just (s,t) ->
>     Tl : etaQuoteSp {n} l (e $$ Tl :<: ev (t (e $$ Hd))) as 
>   Nothing -> error "The impossible happened in etaQuoteSp (Tl)"
> etaQuoteSp {n} l (e :<: t) (Out : as) = case outable t of
>   Just ty' ->
>     Out : etaQuoteSp {n} l (e $$ Out :<: ev ty') as 
>   Nothing -> error "The impossible happened in etaQuoteSp (Out)"
> etaQuoteSp {n} l (p :<: PRF _P) (QA x y q : as) = case evv _P of
>   EQ (PI _S _T) f (PI _S' _T') g  ->
>     let  x' = etaQuoten {n} l (ev _S :>: x)
>          y' = etaQuoten {n} l (ev _T :>: y)
>          q' = etaQuoten {n} l (PRF (EQ (exp _S) x (exp _S') y) :>: q)
>     in   QA (exp x') (exp y') (exp q') : 
>            etaQuoteSp {n} l (p $$ QA x y q :<: 
>                                PRF (EQ (_T $$. x) (f $$. x) 
>                                        (_T' $$. y) (g $$. y))) as
>   _ ->  error "The impossible happened in etaQuoteSp (QA)"
> etaQuoteSp {n} l (p :<: PRF _P) (Sym : as) = case ev _P of
>   EQ _S s _T t  -> Sym : etaQuoteSp {n} l (p $$ Sym :<: PRF (EQ _T t _S s)) as
>   SETEQ _S _T  -> Sym : etaQuoteSp {n} l (p $$ Sym :<: PRF (SETEQ _T _S)) as
>   _ ->  error "The impossible happened in etaQuoteSp (Sym)"
> etaQuoteSp {n} l (e :<: LABEL _T _) (Call lab : as) = 
>   let  lab' = etaQuoten {n} l (ev _T :>: lab)  
>   in   Call (exp lab') : etaQuoteSp {n} l (e $$ Call lab :<: ev _T) as

> etahQuote :: pi (n :: Nat) . Int -> Tm {Head, Val, Z} -> (Tm {Head, Val, n} :<: TY)
> etahQuote {n} l' (P (l, x, s)) = case levi {n} (l-l') of
>   Nothing -> P (l, x, s) :<: s
>   Just i -> (V i :<: s)
> etahQuote {n} l (Refl _S s) = 
>   Refl (exp $ etaQuoten {n} l (SET :>: _S)) (exp $ etaQuoten {n} l (ev _S :>: s)) 
>    :<: PRF (EQ _S s _S s)
> etahQuote {n} l (SetRefl _S) = 
>   SetRefl (exp $ etaQuoten {n} l (SET :>: _S))
>    :<: PRF (SETEQ _S _S)
> etahQuote {n} l (Coeh coeh _S _T q s) =
>     Coeh coeh (exp $ etaQuoten {n} l (SET :>: _S)) 
>               (exp $ etaQuoten {n} l (SET :>: _T))
>               (exp $ etaQuoten {n} l (PRF (SETEQ _S _T) :>: q))
>               (exp $ etaQuoten {n} l (ev _S :>: s)) 
>       :<: eorh coeh
>  where eorh :: Coeh -> EXP
>        eorh Coe = _S
>        eorh Coh = PRF (EQ _S s _T (Coeh Coe _S _T q s :$ B0))
> etahQuote {n} l (D def) = D def :<: defTy def 
> etahQuote {n} l (B d@(SIMPLDTY name _I uDs)) = B d :<: _I --> SET
> etahQuote {n} l x = error $ ugly V0 x    

> etaQuoteTEL :: pi (n :: Nat) . Int -> (VAL :>: [EXP]) -> [Tm {Body, Exp, n}]
> etaQuoteTEL {n} l (ONE :>: []) = []
> etaQuoteTEL {n} l (SIGMA s t :>: e : es) = 
>  exp (etaQuoten {n} l (ev s :>: e)) : etaQuoteTEL {n} l (ev (t $$. e) :>: es)
