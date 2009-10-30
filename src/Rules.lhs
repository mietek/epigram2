\section{Rules}
\label{sec:rules}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, PatternGuards #-}

> module Rules where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable
> import Data.Traversable
> import Data.List

> import BwdFwd
> import Tm
> import Root
> import Rooty
> import Features
> import MissingLibrary

%endif

\subsection{Type-directed operations}

Historically, canonical terms were type-checked by the following
function:

< canTy :: (t -> VAL) -> (Can VAL :>: Can t) -> Maybe (Can (TY :>: t))
< canTy ev (Set,Set)    = Just Set
< canTy ev (Pi s t,Set) = Just (Pi (SET :>: s) ((Arr (ev s) SET) :>: t)
< canTy _  _            = Nothing


If we temporally forget Features, we have here a type-checker that
takes an evaluation function |ev|, a type, and a term to be checked
against this type. When successful, the result of typing is a
canonical term that contains both the initial term and its normalized
form, as we get it during type-checking.

However, in order to implement tactics, we have to generalize this
function. The generalization consists in parameterizing |canTy| with a
type-directed function |(TY :>: t) -> s|, which is equivalent to 
|TY -> t -> s|. Because we are still using the concept of evaluation, both
functions are fused into a single one, of type: 
|TY -> t -> (s,VAL)|. To support the use of tactics, which can fail to produce a
value, we extend this type to |TY -> t -> Maybe (s,VAL)|

Hence, by defining an appropriate function |tc|, we can recover the
previous definition of |canTy|. We can also do much more: intuitively,
we can write any type-directed function in term of |canTy|. That is,
any function traversing the types derivation tree can be expressed
using |canTy|. 

> canTy :: (TY -> t -> Maybe (s, VAL)) -> (Can VAL :>: Can t) -> Maybe (Can s)
> canTy tc (Set :>: Set)     =  Just Set
> canTy tc (Set :>: Pi s t)  =
>   SET         `tc` s &\ \ s sv ->
>   Arr sv SET  `tc` t &\ \ t _ ->
>   Just $ Pi s t
> import <- CanTyRules
> canTy  _  _                 = Nothing




> elimTy :: (t -> VAL) -> (VAL :<: Can VAL) -> Elim t ->
>           Maybe (Elim (TY :>: t),VAL)
> elimTy ev (f :<: Pi s t) (A e) = Just (A (s :>: e),t $$ A (ev e)) 
> import <- ElimTyRules
> elimTy _  _              _     = Nothing


\subsection{Quotation}


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

The role of |quoteRef tm v| is to bind the free variable |v| in |tm|
to the bound variable 0. Hence, it turns a |VV|alue into a |TT|erm.

> quoteRef :: Rooty m => [REF] -> Tm {d,VV} REF -> m (Tm {d,TT} REF)
> quoteRef  refs (P x) =
>     case x `elemIndex` refs of
>       Just i -> pure $ V $ length refs - i - 1
>       Nothing -> pure $ P x
> quoteRef refs (L (H vs x t)) = 
>     (|(\t -> L (x :. t))
>       (Rooty.freshRef (x :<: undefined) 
>                       (\x -> quoteRef (x:refs) 
>                                        (eval t (vs :< pval x))))|)
> quoteRef refs (L (K t)) = (|(L . K) (quoteRef refs t) |)
> quoteRef refs (C c) = (|C (traverse (quoteRef refs) c )|)
> quoteRef refs (N n) = (|N (quoteRef refs n)|)
> quoteRef refs (n :$ v) = (|(:$) (quoteRef refs n)
>                                 (traverse (quoteRef refs) v)|)
> quoteRef refs (op :@ vs) = (|(:@) (pure op)
>                                   (traverse (quoteRef refs) vs)|)


> etaExpand :: (TY :>: VAL) -> Root -> Maybe INTM
> etaExpand (C (Pi s t) :>: f) r = Just $
>   L ("" :. fresh ("" :<: s) (\v  -> inQuote (t $$ A v :>: (f $$ A v))) r)
> import <- EtaExpand
> etaExpand _                  _ = Nothing

> inQuote :: (TY :>: VAL) -> Root -> INTM
> inQuote tyv              r | Just t    <- etaExpand tyv r = t
> inQuote (_ :>: N n)      r | (t :<: _) <- exQuote n r = N t
> inQuote (C cty :>: C cv) r
>   | Just ct   <- canTy (\ y v -> Just (inQuote (y :>: v) r, v)) (cty :>: cv)
>   = C ct

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



\subsection{Type inference}

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


\subsection{Type checking}


> check :: (TY :>: INTM) -> Root -> Maybe ()
> check (C c :>: C c')        r = do
>   csp <- canTy (\ y t -> Just (check (y :>: t) r, evTm t)) (c :>: c')
>   traverse id csp
>   return ()
> check (C (Pi s t) :>: L sc) r = do
>   Root.freshRef ("" :<: s) 
>            (\ref -> check (t $$ A (pval ref) :>: underScope sc ref)) 
>            r
> check (w :>: N n)           r = do
>   y <- infer n r
>   guard $ equal (SET :>: (w, y)) r
>   return ()
> import <- Check
> check _                     _ = Nothing




\subsection{Operators}

> import <- OpCode

> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

\subsection{Equality?}

> mkEqConj :: [(TY :>: VAL,TY :>: VAL)] -> VAL
> mkEqConj ((y0 :>: t0,y1 :>: t1) : []) = eqGreen @@ [y0,t0,y1,t1]
> mkEqConj ((y0 :>: t0,y1 :>: t1) : xs) = 
>   AND (eqGreen @@ [y0,t0,y1,t1]) (mkEqConj xs)
> mkEqConj []                           = TRIVIAL

> eqGreenT :: (InTm x :>: InTm x) -> (InTm x :>: InTm x) -> InTm x
> eqGreenT (y0 :>: t0) (y1 :>: t1) = N (eqGreen :@ [y0,t0,y1,t1])

> opRunEqGreen :: [VAL] -> Either NEU VAL
> opRunEqGreen [SET,C t0,SET,C t1] = case halfZip t0' t1' of
>    Nothing -> Right ABSURD
>    Just x  -> Right $ mkEqConj (trail x)
>    where
>    Just t0' = canTy (\ y v -> Just (y :>: v, v)) (Set :>: t0)
>    Just t1' = canTy (\ y v -> Just (y :>: v, v)) (Set :>: t1)
> import <- OpRunEqGreen
> opRunEqGreen [C (Pi s1 t1),f1,C (Pi s2 t2),f2] = Right $
>   eval  [.s1.t1.f1.s2.t2.f2.
>         ALL (NV s1) . L $ "" :. [.x1.
>         ALL (NV s2) . L $ "" :. [.x2.
>         IMP (EQBLUE (NV s2 :>: NV x2) (NV s1 :>: NV x1))
>             (eqGreenT (t1 $# [x1] :>: f1 $# [x1]) (t2 $# [x2] :>: f2 $# [x2]))
>         ]]]
>         $ B0 :< s1 :< t1 :< f1 :< s2 :< t2 :< f2

%if False

> {-
>    ALL s1 (L (H (bwdList [s1,t1,f1,s2,t2,f2])
>                 "" 
>                 (ALL (NV 3) -- s2
>                      (L ("" 
>                          :. 
>                          (IMP (EQBLUE (NV 7 :>: NV 1)  -- s1 :>: x1
>                                       (NV 4 :>: NV 0)) -- s2 :>: x2
>                               (N (eqGreen :@ [N (V 5 :$ A NV 1), -- f1 x1
>                                               N (V 6 :$ A NV 1), -- t1 x1
>                                               N (V 2 :$ A NV 0), -- f2 x2
>                                               N (V 3 :$ A NV 0)] -- t2 x2
>                                  ))))))))
> -}

%endif

> opRunEqGreen [SET,N t0,SET,_] = Left t0
> opRunEqGreen [SET,_,SET,N t1] = Left t1
> opRunEqGreen [N y0,_,_,_] = Left y0
> opRunEqGreen [_,_,N y1,_] = Left y1
> opRunEqGreen [C y0,_,C y1,_] = Right TRIVIAL

> coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> VAL
> coerce (Pi (x1,x2) (y1,y2))    q f = 
>              eval [.x1.x2.y1.y2.q.f.
>                   (L $ "" :. [.s1.
>                     (let
>                     s2 = N (coe :@ [NV x2,NV x1,N (V q :$ Fst),NV s1])
>                     q2 = N (coh :@ [NV x2,NV x1,N (V q :$ Fst),NV s1])
>                     in
>                     N $ coe :@ [N (V y2 :$ A s2),
>                                 y1 $# [s1],
>                                 N (V q :$ A s2 :$ A (NV s1) :$ A q2),
>                                 N (V f :$ A s2)])])]
>                    (B0 :< x1 :< x2 :< y1 :< y2 :< q :< f)
> import <- Coerce
