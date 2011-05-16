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

> import Kit.BwdFwd
> import Kit.NatFinVec
> import Kit.MissingLibrary 

%endif


> distillPS :: (EXP :>: EXP) -> ProofState DInTmRN
> distillPS (ty :>: tm) = do
>     lev <- getDevLev
>     distill (ev ty :>: ev tm) lev


> distill :: (Applicative m, MonadError StackError m) => 
>              VAL :>: VAL -> Int -> m DInTmRN
> distill (ty :>: L g n b) l = case fromJust $ lambdable ty of
>   (k, s, t) -> 
>     (| (DLAV n) (distill (ev (t (P (l, n, s) :$ B0)) 
>                           :>: ((g <:< (P (l, n, s) :$ B0)) // b)) (l + 1))
>     |)
> distill (ty :>: LK b) l = case fromJust $ lambdable ty of
>   (_, s, t) -> 
>      (| DLK  (distill (ev (t (P (l,"s",s) :$ B0)) :>: ev b) (l+1))
>      |)

> distill (ty :>: h@(D d s _)) l = case lambdable ty of
>   Just (k, s, t) -> 
>     (| (DLAV "x") (distill (ev (t (P (l, "x", s) :$ B0)) 
>                              :>: (h $$. (P (l, "x", s) :$ B0))) (l + 1))
>     |)
>   Nothing -> do
>     let dh  =  DP (nameToRelName (defName d))
>         ty  =  defTy d
>         ss  =  map A (rewindStk s [])
>     das <- distillSpine (ev ty :>: (h, ss)) l
>     (| (DN (dh ::$ das)) |)

> distill (ty :>: h :$ as) l = do
>     (dh, ty, ss) <- distillHead h
>     das <- distillSpine (ev ty :>: (h :$ B0, ss ++ trail as)) l
>     return $ DN (dh ::$ das)

> distill ((tyc :- tyas) :>: (c :- as)) l = case canTy ((tyc , tyas) :>: c) of
>   Nothing -> throwError' $ err "Tin thadger wasp unit"
>   Just tel -> (| (DC c) (distillCan (tel :>: as) l) |)


> distill tt _ = throwError' $ err $ "Distiller can't cope with " ++ show tt

> distillCan :: (Applicative m, MonadError StackError m) => 
>                 (VAL :>: [EXP]) -> Int -> m [DInTmRN]
> distillCan (ONE :>: []) l = (| [] |)
> distillCan (SIGMA s t :>: a : as) l = 
>   (| (distill (ev s :>: ev a) l) : (distillCan (ev (t $$ A a) :>: as) l) |)


> distillHead :: (Applicative m, MonadError StackError m) => 
>                  Tm {p, s, Z} -> m (DHead RelName, TY, [Elim EXP])
> distillHead (P (l', n, s)) = return (DP [(n,Abs l')], s, [])
> distillHead (D def ss op)  = return (DP (nameToRelName (defName def)),
>                                      defTy def,
>                                      map A (rewindStk ss []))
> distillHead t = throwError' $ err $ "distillHead: barf " ++ show t


> distillSpine :: (Applicative m, MonadError StackError m) => 
>                   VAL :>: (VAL, [Elim (Tm {Body, Exp, Z})]) -> 
>                   Int -> m [Elim DInTmRN]
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
