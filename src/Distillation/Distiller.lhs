\section{The distiller}
\label{sec:Distillation.Distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards, FlexibleContexts #-}

> module Distillation.Distiller where

> import Control.Applicative
> import Control.Monad.Error

> import Data.Maybe

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.TypeCheckRules
> import Evidences.ErrorHandling

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import ProofState.Structure.Developments
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Interface.NameResolution

> import Kit.BwdFwd
> import Kit.NatFinVec
> import Kit.MissingLibrary 

%endif


> distillPS :: (EXP :>: EXP) -> ProofState DInTmRN
> distillPS (ty :>: tm) = do
>     lev <- getDevLev
>     distill (ev ty :>: ev tm) (lev, B0)


> distill :: VAL :>: VAL -> (Int, Bwd (Int, String, TY)) -> ProofState DInTmRN
> distill (ty :>: L g n b) (l,ps) = case fromJust $ lambdable ty of
>   (k, s, t) -> 
>     (| (DLAV n) (distill (ev (t (P (l, n, s) :$ B0)) 
>                           :>: ((g <:< (P (l, n, s) :$ B0)) // b)) 
>                   (l + 1,ps:<(l,n,s)))
>     |)
> distill (ty :>: LK b) l = case fromJust $ lambdable ty of
>   (_, s, t) -> 
>      (| DLK  (distill (ev (t (error "LKdistill")) :>: ev b) l)
>      |)

> distill (ty :>: h@(D d sd _)) (l,ps) = do
>   (nom, ty, as) <- unresolveD d ps (bwdList $ map A $ rewindStk sd [])
>   let ty'  =  maybe (defTy d) id ty
>   das <- distillSpine (ev ty' :>: (h, as)) (l,ps)
>   (| (DN (DP nom ::$ das)) |)

> distill (ty :>: h :$ as) l = do
>     (dh, ty, ss) <- distillHead h l
>     das <- distillSpine (ev ty :>: (h :$ B0, ss ++ trail as)) l
>     return $ DN (dh ::$ das)

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
>   Just tel -> (| (DC c) (distillCan (tel :>: as) l) |)


> distill tt _ = throwError' $ err $ "Distiller can't cope with " ++ show tt

> distillCan :: (VAL :>: [EXP]) -> (Int, Bwd (Int, String, TY)) -> ProofState [DInTmRN]
> distillCan (ONE :>: []) l = (| [] |)
> distillCan (SIGMA s t :>: a : as) l = 
>   (| (distill (ev s :>: ev a) l) : (distillCan (ev (t $$ A a) :>: as) l) |)


> distillHead :: Tm {p, s, Z} -> (Int,Bwd (Int, String, TY)) ->  ProofState (DHead RelName, TY, [Elim EXP])
> distillHead (P (l', n, s)) (l,es) = do
>   r <- unresolveP (l', n, s) es 
>   return (DP r, s, [])
> distillHead (D def ss op)  (l,es) = do
>   (nom, ty, as) <- unresolveD def es (bwdList $ map A $ rewindStk ss [])
>   return (DP nom, maybe (defTy def) id ty, as)

> -- [Feature = Equality]
> distillHead (Refl _T t) l = do
>   _T' <- distill (SET :>: ev _T) l
>   t' <- distill (ev _T :>: ev t) l
>   (| (DRefl _T' t', PRF (EQ _T t _T t), []) |)
> distillHead (Coeh coeh _S _T q s) l = do
>     _S' <- distill (SET :>: ev _S) l
>     _T' <- distill (SET :>: ev _T) l
>     q' <- distill (PRF (EQ SET _S SET _T) :>: ev q) l
>     s' <- distill (ev _S :>: ev s) l
>     (| (DCoeh coeh _S' _T' q' s', eorh coeh _S _T q s, []) |)
>   where
>     eorh :: Coeh -> EXP -> EXP -> EXP -> EXP -> EXP
>     eorh Coe _ _T' _ _ = _T'
>     eorh Coh _S' _T' q' s' = 
>       PRF (EQ _S' s' _T' (Coeh Coe _S' _T' q' s' :$ B0))
>     
> -- [/Feature = Equality]

> distillHead t _ = throwError' $ err $ "distillHead: barf " ++ show t


> distillSpine :: VAL :>: (VAL, [Elim (Tm {Body, Exp, Z})]) -> 
>                 (Int, Bwd (Int, String, TY)) -> ProofState [Elim DInTmRN]
> distillSpine (_ :>: (_, [])) _ = (| [] |)
> distillSpine (ty :>: (h :$ az, A a : as)) l = case fromJust $ lambdable ty of 
>   (k, s, t) -> do
>     a' <- (distill (ev s :>: (ev a)) l)
>     as' <- distillSpine (ev (t a) :>: (h :$ (az :< A a), as)) l
>     return $ A a' : as'
> distillSpine (ty :>: (h :$ az , Hd : as)) l = case fromJust $ projable ty of
>   (s, t) -> 
>     (| (Hd :) 
>        (distillSpine (ev s :>: (h :$ (az :< Hd) , as)) l)
>     |)
> distillSpine (ty :>: (h :$ az , Tl : as)) l = case fromJust $ projable ty of
>   (s, t) -> 
>     (| (Tl :) 
>        (distillSpine (ev (t (h :$ (az :< Hd))) :>: (h :$ (az :< Tl) , as)) l)
>     |)
> -- [Feature = Equality]
> distillSpine (PRF _P :>: (tm, QA x y q : as)) l
>           | EQ _S f _T g <- ev _P
>           , Just (_, _SD, _SC) <- lambdable (ev _S)  
>           , Just (_, _TD, _TC) <- lambdable (ev _T) = do
>       x' <- distill (ev _SD :>: ev x) l
>       y' <- distill (ev _TD :>: ev y) l
>       q' <- distill (PRF (EQ _SD x _TD y) :>: ev q) l
>       (| (QA x' y' q' :) 
>            (distillSpine (PRF (EQ (_SC x) (f $$. x) (_TC y) (g $$. y)) :>: 
>                      (tm $$ (QA x y q), as)) l) |)
>
> distillSpine (PRF _P :>: (tm, Sym : as)) l | EQ _S s _T t <- ev _P =
>   (| (Sym :) (distillSpine (PRF (EQ _T t _S s) :>: (tm $$ Sym, as)) l) |)

> -- [/Feature = Equality]
> distillSpine _ _  = throwError' (err "Deep!")
