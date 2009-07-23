\section{Rules}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, PatternGuards #-}

> module Rules where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable
> import Data.Traversable
> import BwdFwd
> import Tm
> import Root
> import Features
> import MissingLibrary

%endif

> canTy :: (t -> VAL) -> (Can VAL :>: Can t) -> Maybe (Can (TY :>: t))
> canTy ev (Set :>: Set)    = Just Set
> canTy ev (Set :>: Pi s t) = 
>   Just (Pi (SET :>: s) (Arr (ev s) SET :>: t))
> import <- CanTyRules
> canTy _  _                = Nothing

> elimTy :: (t -> VAL) -> (VAL :<: Can VAL) -> Elim t ->
>           Maybe (Elim (TY :>: t),VAL)
> elimTy ev (f :<: Pi s t) (A e) = Just (A (s :>: e),t $$ A (ev e)) 
> import <- ElimTyRules
> elimTy _  _              _     = Nothing

> quop :: REF -> Root -> EXTM
> quop ref@(ns := _) r = help (bwdList ns) r
>   where 
>   help (ns :< (_,i)) (r,j) = if ns == r then V (j-i-1) else P ref

> bquote :: Tm {d,VV} REF -> Root -> Tm {d,TT} REF
> bquote (L (H vs x t)) r = 
>   L (x :. fresh (x :<: undefined) (\x -> bquote (eval t (vs :< x))) r)
> bquote (L (K t))      r = L (K (bquote t r))
> bquote (C c)          r = C (traverse bquote c r)
> bquote (N n)          r = N (bquote n r)
> bquote (P x)          r = quop x r
> bquote (n :$ v)       r = bquote n r :$ traverse bquote v r
> bquote (op :@ vs)     r = op :@ traverse bquote vs r

> etaExpand :: (TY :>: VAL) -> Root -> Maybe INTM
> etaExpand (C (Pi s t) :>: f) r = Just $
>   L ("" :. fresh ("" :<: s) (\v  -> inQuote (t $$ A v :>: (f $$ A v))) r)
> import <- EtaExpand
> etaExpand _                  _ = Nothing

> inQuote :: (TY :>: VAL) -> Root -> INTM
> inQuote tyv              r | Just t    <- etaExpand tyv r = t
> inQuote (_ :>: N n)      r | (t :<: _) <- exQuote n r = N t
> inQuote (C cty :>: C cv) r | Just x    <- canTy id (cty :>: cv) =
>   C (traverse inQuote x r)

> unC :: VAL -> Can VAL
> unC (C c) = c

> exQuote :: NEU -> Root -> (EXTM :<: TY)
> exQuote (P x)       r = quop x r :<: pty x
> exQuote (n :$ v)    r = (n' :$ traverse inQuote e r) :<: ty'
>   where
>   (n' :<: ty)  = exQuote n r
>   Just (e,ty') = elimTy id (N n :<: unC ty) v
> exQuote (op :@ vs)  r = (op :@ traverse inQuote vs' r) :<: v where
>    Just (vs',v) = opTy op id vs 

> quote :: (TY :>: VAL) -> Root -> INTM
> quote vty r = inQuote vty (room r "quote")

> equal :: (TY :>: (VAL,VAL)) -> Root -> Bool
> equal (ty :>: (v1,v2)) r = quote (ty :>: v1) r == quote (ty :>: v2) r

> infer :: EXTM -> Root -> Maybe TY
> infer (P x)              r = Just (pty x)
> infer (t :$ s)           r = do
>   C ty <- infer t r
>   (s',ty') <- elimTy evTm (evTm t :<: ty) s
>   traverse id $ traverse check s' r
>   return ty'
> infer (op :@ ts)         r = do
>   (vs,v) <- opTy op evTm ts
>   traverse id $ traverse check vs r
>   return v
> infer (t :? ty)          r = do
>   check (SET :>: ty) r
>   let vty = evTm ty
>   check (vty :>: t) r
>   return vty
> infer _                  _ = Nothing

> check :: (TY :>: INTM) -> Root -> Maybe ()
> check (C c :>: C c')        r = do
>   x <- canTy evTm (c :>: c')
>   traverse id $ traverse check x r
>   return ()
> check (C (Pi s t) :>: L sc) r = do
>   freshRef ("" :<: s) 
>            (\ref -> check (t $$ A (pval ref) :>: underScope sc ref)) 
>            r
> check (w :>: N n)           r = do
>   y <- infer n r
>   guard $ equal (SET :>: (w, y)) r
>   return ()
> import <- Check
> check _                     _ = Nothing

> import <- OpCode

> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

> mkEqConj :: [(TY :>: VAL,TY :>: VAL)] -> VAL
> mkEqConj ((y0 :>: t0,y1 :>: t1) : []) = eqGreen @@ [y0,t0,y1,t1]
> mkEqConj ((y0 :>: t0,y1 :>: t1) : xs) = 
>   AND (eqGreen @@ [y0,t0,y1,t1]) (mkEqConj xs)
> mkEqConj []                           = TRIVIAL

> opRunEqGreen :: [VAL] -> Either NEU VAL
> opRunEqGreen [SET,C t0,SET,C t1] = case halfZip t0' t1' of
>    Nothing -> Right ABSURD
>    Just x  -> Right $ mkEqConj (trail x)
>    where
>    Just t0' = canTy id (Set :>: t0)
>    Just t1' = canTy id (Set :>: t1)
> import <- OpRunEqGreen
> opRunEqGreen [SET,N t0,SET,_] = Left t0
> opRunEqGreen [SET,_,SET,N t1] = Left t1
> opRunEqGreen [N y0,_,_,_] = Left y0
> opRunEqGreen [_,_,N y1,_] = Left y1
> opRunEqGreen [C y0,_,C y1,_] = Right TRIVIAL
