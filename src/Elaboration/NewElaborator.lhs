%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards, RankNTypes, KindSignatures #-}

> module Elaboration.NewElaborator where

> import Prelude hiding (exp)

> import Kit.NatFinVec
> import Kit.BwdFwd

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import Evidences.Tm
> import Evidences.Primitives
> import Evidences.NameSupply
> import Evidences.ErrorHandling

> import DisplayLang.Name
> import DisplayLang.Scheme

> import SourceLang.Parx
> import SourceLang.Lexer
> import SourceLang.SourceData
> import Elaboration.NewElabMonad
> import Elaboration.NewRunElab

%endif

> instance Problem EpiInTm where
>   probName x = "elabInTm"
>   probTel x = SET *** ONE
>   probVal x [_S] = exp _S *** ONE
>   probElab (EEx ex) [_Sf] = do
>     f <- eElab ("ex" :<: return (ex, []))
>     (_S'f, s'f) <- eSplit f
>     [_S,_S'] <- eLatests [_Sf, _S'f]
>     h <- eHope ("eq" :<: return (SETEQ (exp _S') (exp _S)))
>     [_S,_S',eq,s'] <- eLatests [_Sf, _S'f, h, s'f]
>     (| (Coeh Coe (exp _S') (exp _S) (exp eq) (exp s') :$ B0) |)    

>   probElab (ELam (_ :~ Sig [] (_ :~ VarConc (_ :~ x) [] Nothing)) body) [_Sf] = do
>     _S <- eLatest _Sf  
>     case _S of
>       PI _A _B -> do
>         ff <- eElab ("body" :<: do  a <- seLambda ("a" :<: _A)
>                                     seLambda ("adub" :<: DUB x (SCHTY _A) (exp a))
>                                     (| (body, [_B $$. a]) |))
>         f <- eLatest ff
>         (| (la "a" $ \a -> nix f :$ (B0 :< A a :< A ZERO :< Hd)) |)

>   probElab e [_S] = error $ show e -- "intm error"

> instance Problem EpiExTm where
>   probName x = "elabExTm"
>   probTel x = ONE
>   probVal x [] = ("S", SET) -** \_S -> _S
>   probElab (EVS f as) [] = do
>     _Sff <- eElab ("f" :<: (| (f, []) |)) 
>     (_Sf, ff) <- eSplit _Sff 
>     [_S, f] <- eLatests [_Sf, ff]
>     _Txf <- eElab ("as" :<: (| (as, [exp _S, exp f]) |)) 
>     PAIR _T x <- eLatest _Txf
>     (| (PAIR _T x) |)

> instance Problem Template where
>   probName x = "Template"
>   probTel x = ONE
>   probVal x [] = ("S", SCHEME) -** \_S -> wr (def schElDEF) _S
>   probElab t [] = do
>     (sf :<: _Sf) <- eDub t
>     [s, _S] <- eLatests [sf, _Sf]
>     (| (PAIR (exp _S) (exp s)) |)

> instance Problem [Elt :~ EpiElim] where
>   probName x = "elabSpine"
>   probTel x = ("S", SCHEME) -** \_S -> wr (def schElDEF) _S *** ONE
>   probVal x _ = ("S", SET) -** \_S -> _S
>   probElab es [_Sf, ff] = do 
>     cfs <- eCan _Sf
>     case (cfs, es) of
>       ((SchTy, [_Tf]), []) -> (| PAIR (| exp (eLatest _Tf) |) 
>                                       (| exp (eLatest ff) |) |)
>       ((SchTy, [_Tf]), _) -> error "elabSpine proj"
>       ((SchPi, [_Sf, _Tf]), (elt :~ EA a : es)) -> do
>         _S <- eLatest _Sf
>         sf <- eElab ("s" :<: return (elt :~ ESch a, [exp _S]))
>         [_T, f, s] <- eLatests [_Tf, ff, sf]
>         rf <- eElab ("t" :<: return (es,  [ exp _T $$. (s $$ Hd)
>                                           , exp f $$. (s $$ Hd)]))
>         (| exp (eLatest rf) |)
>       ((SchImPi, [_Sf, _Tf]), _) -> do
>         _S <- eLatest _Sf
>         sf <- eHope ("s" :<: return (exp _S))
>         [_T, f, s] <- eLatests [_Tf, ff, sf]
>         rf <- eElab ("t" :<: return (es, [exp _T $$. s, exp f $$. s]))
>         (| exp (eLatest rf) |)
>       _ -> eCry [err "elabSpine"]

> newtype ESch = ESch EpiInTm

> instance Problem ESch where
>   probName x = "elabSch"
>   probTel x = SCHEME *** ONE
>   probVal x [_S] = wr (def schElDEF) (exp _S) *** ONE
>   probElab (ESch a) [_Sf] = do 
>     cfs <- eCan _Sf
>     case cfs of
>       (SchTy, [_Tf]) -> do
>          _T <- eLatest _Tf 
>          af <- eElab ("escht" :<: return (a, [exp _T]))
>          (| exp (eLatest af) |)
>       (SchPi, [_Sf, _Tf]) -> do
>          [_S,_T] <- eLatests [_Sf, _Tf]
>          ff <- eElab ("eschi" :<: do 
>             s <- seLambda ("s" :<: exp _S) 
>             return (ESch a, [exp $ _T $$. s]))
>          f <- eLatest ff
>          (| (PAIR (L ENil "s" (nix f :$ (B0 :< A (V Fz :$ B0) :< Hd))) ZERO) |)
>       (SchImPi, [_Sf, _Tf]) -> case a of
>         ELam (_ :~ Sig [] (_ :~ VarConc (_ :~ x) [] Nothing)) (e :~ t) -> do 
>           [_S,_T] <- eLatests [_Sf, _Tf]
>           ff <- eElab ("eschi" :<: do 
>              s <- seLambda ("s" :<: exp _S) 
>              seLambda ("sdub" :<: DUB x (exp _S) (exp s)) 
>              return (e :~ (ESch t), [exp $ _T $$. s]))
>           f <- eLatest ff
>           (| (PAIR (L ENil "s" (nix f :$ (B0 :< A (V Fz :$ B0) :< A ZERO :< Hd))) ZERO) |)

>         _ -> error "Sch error" -- cry?

> instance Problem t => Problem (x :~ t) where
>   probName (_ :~ x) = "sourced" ++ probName x
>   probTel (_ :~ x) = probTel x
>   probVal (_ :~ x) es = probVal x es
>   probElab (_ :~ x) fs = probElab x fs
