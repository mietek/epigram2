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

> distill (ty :>: h :$ as) (l, es) = do
>     (dh, ty, ss) <- distillHead h es
>     das <- distillSpine (ev ty :>: (h :$ B0, ss ++ trail as)) (l, es)
>     return $ DN (dh ::$ das)

> distill ((tyc :- tyas) :>: (c :- as)) l = case canTy ((tyc , tyas) :>: c) of
>   Nothing -> throwError' $ err "Tin thadger wasp unit"
>   Just tel -> (| (DC c) (distillCan (tel :>: as) l) |)


> distill tt _ = throwError' $ err $ "Distiller can't cope with " ++ show tt

> distillCan :: (VAL :>: [EXP]) -> (Int, Bwd (Int, String, TY)) -> ProofState [DInTmRN]
> distillCan (ONE :>: []) l = (| [] |)
> distillCan (SIGMA s t :>: a : as) l = 
>   (| (distill (ev s :>: ev a) l) : (distillCan (ev (t $$ A a) :>: as) l) |)


> distillHead :: Tm {p, s, Z} -> Bwd (Int, String, TY) ->  ProofState (DHead RelName, TY, [Elim EXP])
> distillHead (P (l', n, s)) es = do
>   r <- unresolveP (l', n, s) es 
>   return (DP r, s, [])
> distillHead (D def ss op)  es = do
>   (nom, ty, as) <- unresolveD def es (bwdList $ map A $ rewindStk ss [])
>   return (DP nom, maybe (defTy def) id ty, as)
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
> distillSpine _ _  = throwError' (err "Deep!")
