\section{The distiller}
\label{sec:Distillation.Distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards, FlexibleContexts #-}

> module Distillation.Distiller where

> import Prelude hiding (exp)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error

> import Data.Maybe

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.TypeCheckRules
> import Evidences.ErrorHandling

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.PrettyPrint

> import ProofState.Structure
> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.NameResolution

> import Kit.BwdFwd
> import Kit.NatFinVec
> import Kit.MissingLibrary 

> import Text.PrettyPrint.HughesPJ (Doc)

%endif


> distillPS :: (EXP :>: EXP) -> ProofState DInTmRN
> distillPS (ty :>: tm) = do
>     lev <- getDevLev
>     distill (ev ty :>: ev tm) (lev, B0)


> prettyPS :: (TY :>: EXP) -> ProofState Doc
> prettyPS = prettyPSAt maxBound

> prettyPSAt :: Size -> (TY :>: EXP) -> ProofState Doc
> prettyPSAt size tt = do
>     dtm <- distillPS tt
>     return (pretty dtm size)

> distill :: VAL :>: VAL -> (Int, Bwd (Int, String, TY)) -> ProofState DInTmRN
> distill (ty :>: L g n b) (l,ps) = case lambdable ty of
>   Just (k, s, t) -> 
>     (| (DLAV n) (distill (ev (t (P (l, n, s) :$ B0)) 
>                           :>: ((g <:< (P (l, n, s) :$ B0)) // b)) 
>                   (l + 1,ps:<(l,n,s)))
>     |)
>   Nothing -> throwError' $ err "distillSpine:"
>                            ++ errTyTm (SET :>: exp ty)
>                            ++ err "is not lambdable"
> distill (ty :>: LK b) l = case lambdable ty of
>   Just (_, s, t) -> 
>      (| DLK  (distill (ev (t (error "LKdistill")) :>: ev b) l)
>      |)
>   Nothing -> throwError' $ err "distillSpine:"
>                            ++ errTyTm (SET :>: exp ty)
>                            ++ err "is not lambdable"

We don't always want to do this, but often do want to, go figure:

< distill (ty :>: h@(D d sd (Eat n o))) (l,ps) = 
<   case forlambdabletran (maybe "o" id n) ty of
<     Just (k, x, s, t) -> 
<       (| (DLAV x) (distill (ev (t (P (l, x, s) :$ B0)) 
<                             :>: mkD {Val} d (sd :<!: (P (l, x, s) :$ B0)) o) 
<                     (l + 1,ps:<(l,x,s)))
<       |)


< distill (ty :>: h :$ as) l = do
<     let (h',as') = stripCall h as []
<     (dh, ty, ss, ms) <- distillHead h as' l
<     das <- distillSpine (ev ty :>: (ev h', ss, ms)) l
<     return $ DN (dh ::$ das)

>     -- [Feature = Label]
> distill (ty :>: h :$ as) l = do
>     let (h',as') = stripCall h as []
>     (dh, ty, ss, ms) <- distillHead h' as' l
>     das <- distillSpine (ev ty :>: (toBody h, ss, ms)) l
>     return $ DN (dh ::$ das)
>  where
>     stripCall :: Tm {Head, s, Z} -> Bwd (Elim EXP) -> [Elim EXP] -> 
>                  (Tm {Head, Exp, Z}, [Elim EXP])
>     stripCall h B0 as = (exp h, as)
>     stripCall _ (_ :< Call l) as | hl :$ las <- ev l = 
>       (exp hl, trail las ++ as)  
>     stripCall h (az :< a) as = stripCall h az (a : as)
>     -- [/Feature = Label]

> distill (ENUMT _E :>: tm) l | Just r <- findIndex (ev _E :>: tm) = return r
>   where
>     findIndex :: (VAL :>: VAL) -> Maybe DInTmRN
>     findIndex (CONSE t  _ :>: ZE)  | (TAG s) <- ev t = Just (DTAG s)
>     findIndex (CONSE _        a :>: SU b)  = findIndex (ev a :>: ev b)
>     findIndex _                            = Nothing

> -- [Feature = Equality]
> distill (PROP :>: EQ _S s _T t) l = do
>   _S' <- distill (SET :>: ev _S) l
>   s' <- distill (ev _S :>: ev s) l
>   _T' <- distill (SET :>: ev _T) l
>   t' <- distill (ev _T :>: ev t) l
>   (| (DEq (DTY _S' s') (DTY _T' t')) |)
> -- [/Feature = Equality]

> distill ((tyc :- tyas) :>: (c :- as)) l = case canTy ((tyc , tyas) :>: c) of
>   Nothing -> throwError' $ err "Tin thadger wasp unit"
>                            ++ err "\ncanonical type"
>                            ++ errTyTm (SET :>: (tyc :- tyas))
>                            ++ err "does not admit canonical term"
>                            ++ errTm (c :- as)
>   Just tel -> (| (DC c) (distillCan (tel :>: as) l) |)


> distill tt _ = throwError' $ err $ "Distiller can't cope with " ++ show tt

> distillCan :: (VAL :>: [EXP]) -> (Int, Bwd (Int, String, TY)) -> ProofState [DInTmRN]
> distillCan (ONE :>: []) l = (| [] |)
> distillCan (SIGMA s t :>: a : as) l = 
>   (| (distill (ev s :>: ev a) l) : (distillCan (ev (t $$ A a) :>: as) l) |)


> distillHead :: Tm {p, s, Z} -> [ Elim EXP ] -> (Int,Bwd (Int, String, TY)) -> 
>                ProofState (DHead RelName, TY, [Elim EXP], Maybe Scheme)
> distillHead (P (l', n, s)) as (l,es) = do
>   r <- unresolveP (l', n, s) es 
>   return (DP r, s, as, Nothing)
> distillHead (D def) as (l,es) = do
>   (nom, ty, as', ms) <- unresolveD def es (bwdList  as)
>   return (DP nom, maybe (defTy def) id ty, as', ms)

> -- [Feature = Equality]
> distillHead (Refl _T t) as l = do
>   _T' <- distill (SET :>: ev _T) l
>   t' <- distill (ev _T :>: ev t) l
>   (| (DRefl _T' t', PRF (EQ _T t _T t), as, Nothing) |)
> distillHead (Coeh coeh _S _T q s) as l = do
>     _S' <- distill (SET :>: ev _S) l
>     _T' <- distill (SET :>: ev _T) l
>     q' <- distill (PRF (EQ SET _S SET _T) :>: ev q) l
>     s' <- distill (ev _S :>: ev s) l
>     (| (DCoeh coeh _S' _T' q' s', eorh coeh _S _T q s, as, Nothing) |)
>   where
>     eorh :: Coeh -> EXP -> EXP -> EXP -> EXP -> EXP
>     eorh Coe _ _T' _ _ = _T'
>     eorh Coh _S' _T' q' s' = 
>       PRF (EQ _S' s' _T' (Coeh Coe _S' _T' q' s' :$ B0))
>     
> -- [/Feature = Equality]

> distillHead t _ _ = throwError' $ err $ "distillHead: barf " ++ show t


> distillSpine :: VAL :>: (VAL, [Elim (Tm {Body, Exp, Z})], Maybe Scheme) -> 
>                 (Int, Bwd (Int, String, TY)) -> ProofState [Elim DInTmRN]
> distillSpine (_ :>: (_, [], _)) _ = (| [] |)
> distillSpine (ty :>: (haz, A a : as, Just (SchImplicitPi _ sch))) l = 
>   case lambdable ty of 
>     Just (k, s, t) -> do
>       as' <- distillSpine (ev (t a) :>: (haz $$ A a, as, Just sch)) l
>       return $ as'
>     Nothing -> throwError' $ err "distillSpine:"
>                            ++ errTyTm (SET :>: exp ty)
>                            ++ err "is not lambdable"
> distillSpine (ty :>: (haz, A a : as, sch)) l = 
>   case lambdable ty of 
>     Just (k, s, t) -> do
>       a' <- (distill (ev s :>: (ev a)) l)
>       as' <- distillSpine (ev (t a) :>: (haz $$ A a, as, fmap (stripScheme 1) sch)) l
>       return $ A a' : as'
>     Nothing -> throwError' $ err "distillSpine:"
>                            ++ errTyTm (SET :>: exp ty)
>                            ++ err "is not lambdable"
> distillSpine (ty :>: (haz , Hd : as, _)) l = case projable ty of
>   Just (s, t) -> 
>     (| (Hd :) 
>        (distillSpine (ev s :>: (haz $$ Hd , as, Nothing)) l)
>     |)
>   Nothing -> throwError' $ err "distillSpine:"
>                            ++ errTyTm (SET :>: exp ty)
>                            ++ err "is not projable"
> distillSpine (ty :>: (haz , Tl : as, _)) l = case projable ty of
>   Just (s, t) -> 
>     (| (Tl :) 
>        (distillSpine (ev (t (haz $$ Hd)) :>: (haz $$ Tl , as, Nothing)) l)
>     |)
>   Nothing -> throwError' $ err "distillSpine:"
>                            ++ errTyTm (SET :>: exp ty)
>                            ++ err "is not projable"
> -- [Feature = Equality]
> distillSpine (PRF _P :>: (tm, QA x y q : as, _)) l
>           | EQ _S f _T g <- ev _P
>           , Just (_, _SD, _SC) <- lambdable (ev _S)  
>           , Just (_, _TD, _TC) <- lambdable (ev _T) = do
>       x' <- distill (ev _SD :>: ev x) l
>       y' <- distill (ev _TD :>: ev y) l
>       q' <- distill (PRF (EQ _SD x _TD y) :>: ev q) l
>       (| (QA x' y' q' :) 
>            (distillSpine (PRF (EQ (_SC x) (f $$. x) (_TC y) (g $$. y)) :>: 
>                      (tm $$ (QA x y q), as, Nothing)) l) |)
>
> distillSpine (PRF _P :>: (tm, Sym : as, _)) l | EQ _S s _T t <- ev _P =
>   (| (Sym :) (distillSpine (PRF (EQ _T t _S s) :>: (tm $$ Sym, as, Nothing)) l) |)
>
> distillSpine (PRF _P :>: (tm, Out : as, _)) l
>     |  EQ _S s _T t    <- ev _P
>     ,  (_Sc :- _Sas)   <- ev _S
>     ,  (_Tc :- _Tas)   <- ev _T 
>     ,  Just (Con, [q])  <- eqUnfold ((_Sc, _Sas) :>: s)
>                                        ((_Tc, _Tas) :>: t) =
>   (| (Out :) (distillSpine (PRF q :>: (tm $$ Out, as, Nothing)) l) |)
> -- [/Feature = Equality]
> distillSpine (_ :>: (_, (t : _), _)) _  = throwError' (err $ "dS: " ++ show t)
