
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
> import Evidences.TmJig
> import Evidences.TypeChecker

%endif

> levi :: pi (n :: Nat) . Int -> Maybe (Fin {n})
> levi {n} l = bound {n} (mkInt n - l - 1)

> ty = ("F",(("S", SET) ->> \ _ -> SET)) ->> \_ -> (("S", SET) ->> \ _ -> SET)
> tm = la "y" $ \ x -> x

> ty2 = ARR (SET *** SET) (SET *** SET)

> ty3 = ARR (SET *** SET) (SET *** SET)

> ty4 = ARR ONE ONE

> swap = L ENil "t"  (PAIR (V Fz :$ (B0 :< ONE)) (V Fz :$ (B0 :< ZERO)))
> tm4 = L ENil "t"  (PAIR (V Fz :$ (B0 :< ZERO)) (V Fz :$ (B0 :< ONE)))

> comp = L ENil "g" $ L ENil "f" $ L ENil "x" $ V (Fs (Fs Fz)) :$ (B0 :< (V (Fs Fz) :$ (B0 :< (V Fz :$ B0))))

> tm5 = (ENil :/ comp) :$ (B0 :< swap :< swap)

> etaQuote :: (EXP :>: EXP) -> VAL
> etaQuote (t :>: e) = etaQuoten {Z} (ev t :>: e)

> etaQuoten :: pi (n :: Nat) . (VAL :>: EXP) -> Tm {Body, Val, n}
> etaQuoten {l} (PI s t :>: f) = 
>   L ENil nom (exp (etaQuoten {S l} (ev (t $$ x) :>: f $$ x)))
>   where x :: EXP 
>         x = P (mkInt l, nom, exp s) :$ B0
>         nom = fortran "x" [ev f, ev t] undefined 
> etaQuoten {l} (SIGMA s t :>: p) = 
>   PAIR (exp (etaQuoten {l} (ev s :>: p $$ ZERO))) 
>        (exp (etaQuoten {l} (ev (t $$ s) :>: p $$ ONE)))
> etaQuoten {l} (ONE :>: _) = ZERO
> etaQuoten {l} (t :>: e) = etaQuotev {l} (t :>: ev e)

> etaQuotev :: pi (n :: Nat) . (VAL :>: VAL) -> Tm {Body, Val, n}
> etaQuotev {l} (tc :- as :>: vc :- bs) = case canTy ((tc, as) :>: vc) of
>   Nothing -> error "It will nae fit"
>   Just t  -> vc :- etaQuoteTEL {l} (t :>: bs) 

> etaQuotev {l} (t :>: x :$ es) = 
>   let  (h :<: t) = etahQuote {l} x  
>   in   h :$ bwdList (etaQuoteSp {l} (x :$ B0 :<: ev t) (trail es))

> etaQuoteSp :: pi (n :: Nat) . (VAL :<: VAL) -> [EXP] -> [Tm {Body, Exp, n}]
> etaQuoteSp {n} (e :<: t) [] = []
> etaQuoteSp {n} (e :<: PI s t) (a:as) = exp (etaQuoten {n} (ev s :>: a)) :
>     etaQuoteSp {n} (e $$ a :<: ev (t $$ a)) as
> etaQuoteSp {n} (e :<: SIGMA s t) (p:as) = case ev p of
>   ZERO -> ZERO : etaQuoteSp {n} (e $$ ZERO :<: ev s) as
>   ONE  -> ONE : etaQuoteSp {n} (e $$ ONE :<: ev t $$ (e $$ ZERO)) as 
> etaQuoteSp {n} (e :<: t) es = error $ "erk " ++ ugly V0 e ++ " :<: " ++ ugly V0 t ++ "... " ++ Data.List.concat (map (ugly V0) es)

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
>   (vs :<: SIGMA s t, ZERO) -> (vs :< ZERO :<: ev s) 
>   (vs :<: SIGMA s t, ONE) -> (vs :< ONE) :<: undefined  

<     t :: Tm {Body, Exp, Z}, h :: Tm {Head, Val, n} 
 
<     (vs :< ONE :<: wk t :$ (B0 :< (exp h :$ (vs :< ZERO)))) 

> -}

> etahQuote :: pi (n :: Nat) . Tm {Head, Val, Z} -> (Tm {Head, Val, n} :<: TY)
> etahQuote {n} (P (l, x, s)) = case levi {n} l of
>   Nothing -> error "Dutch level overflow"
>   Just i -> (V i :<: s)

> etaQuoteTEL :: pi (n :: Nat) . (VAL :>: [EXP]) -> [Tm {Body, Exp, n}]
> etaQuoteTEL {l} (ONE :>: []) = []
> etaQuoteTEL {l} (SIGMA s t :>: e : es) = 
>  exp (etaQuoten {l} (ev s :>: e)) : etaQuoteTEL {l} (ev (t $$ e) :>: es)
