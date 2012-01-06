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

> import Debug.Trace

%endif

> instance Problem EpiInTm where
>   probName x = "elabInTm"
>   probTel x = SET *** ONE
>   probVal x [_S] = exp _S *** ONE
>   probElab (EEx ex) [_Sf] = do
>     ff <- eElab ("ex" :<: return (ex, []))
>     (_S'f, s'f) <- eSplit ff
>     [_S,_S'] <- eLatests [_Sf, _S'f]
>     h <- eHope ("eq" :<: return (PRF (SETEQ (exp _S') (exp _S))))
>     [_S,_S',eq,s'] <- eLatests [_Sf, _S'f, h, s'f]
>     (| (PAIR (Coeh Coe (exp _S') (exp _S) (exp eq) (exp s') :$ B0) ZERO) |)   

>   probElab (ELam (_ :~ Sig [] (_ :~ VarConc (_ :~ x) [] Nothing)) body) [_Sf] = do
>     (_Af, _Bf) <- ePi _Sf  
>     [_A,_B] <- eLatests [_Af, _Bf]
>     ff <- eElab ("body" :<: do  a <- seLambda (x :<: exp _A)
>                                 seLambda (x ++ "dub" :<: DUB x (SCHTY (exp _A)) (exp a))
>                                 (| (body, [exp _B $$. a]) |))
>     f <- eLatest ff
>     (| (PAIR (la x $ \a -> nix f :$ (B0 :< A a :< A ZERO :< Hd)) ZERO) |)

>   probElab (EPi (_ :~ Sig [] (_ :~ VarConc (_ :~ "") [] (Just ty))) body) [_Sf] = do
>     -- Is there a better way to spot vac Pis?
>     eSet _Sf
>     _Xf' <- eElab ("X" :<: (| (ty, [SET]) |))
>     (_Xf , _) <- eSplit _Xf'
>     ff <- eElab ("body" :<: (| (body, [SET]) |))
>     [_X, f] <- eLatests [_Xf, ff]
>     (| (PAIR (PI (exp _X) (LK $ nix f :$ (B0 :< Hd))) ZERO) |)

>   probElab (EPi (_ :~ Sig [] (_ :~ VarConc (_ :~ x) [] (Just ty))) body) [_Sf] = do
>     eSet _Sf
>     _Xf' <- eElab ("X" :<: (| (ty, [SET]) |))
>     (_Xf , _) <- eSplit _Xf'
>     _X <- eLatest _Xf
>     ff <- eElab ("body" :<: do  a <- seLambda (x :<: exp _X)
>                                 seLambda (x ++ "dub" :<: DUB x (SCHTY (exp _X)) (exp a))
>                                 (| (body, [SET]) |))
>     [_X, f] <- eLatests [_Xf, ff]
>     (| (PAIR (PI (exp _X) (la x $ \a -> nix f :$ (B0 :< A a :< A ZERO :< Hd))) ZERO) |)

>   probElab ESet [_Sf] = do
>     eSet _Sf
>     (| (PAIR SET ZERO) |) 

>   probElab e [_S] = error $ show e -- "intm error"

> instance Problem EpiExTm where
>   probName x = "elabExTm"
>   probTel x = ONE
>   probVal x [] = ("S", SET) -** \_S -> _S
>   probElab (EVS f as) [] = do
>     _Sff <- eElab ("f" :<: (| (f, []) |))
>     (_Sf, ff) <- eSplit _Sff 
>     [_S, f] <- eLatests [_Sf, ff]
>     _Txf <- eElab ("as" :<: (| (SchSpine as, [exp _S, exp f]) |)) 
>     (_Tf, xf) <- eSplit _Txf
>     (| PAIR (| exp (eLatest _Tf) |) (| exp (eLatest xf) |) |)

> instance Problem Template where
>   probName x = "Template"
>   probTel x = ONE
>   probVal x [] = ("S", SCHEME) -** \_S -> wr (def schElDEF) _S
>   probElab t [] = do
>     (sf :<: _Sf) <- eDub' t
>     [s, _S] <- eLatests [sf, _Sf]
>     (| (PAIR (exp _S) (exp s)) |)

> newtype SchSpine = SchSpine [Elt :~ EpiElim] 
> newtype TySpine = TySpine [Elt :~ EpiElim] 

> instance Problem SchSpine where
>   probName x = "elabSchSpine"
>   probTel x = ("S", SCHEME) -** \_S -> wr (def schElDEF) _S *** ONE
>   probVal x _ = ("S", SET) -** \_S -> _S
>   probElab (SchSpine es) [_Sf, ff] = do 
>     cfs <- eCan _Sf
>     case (cfs, es) of
>       ((SchTy, [_Tf]), as) -> do  
>         [_T, f] <- eLatests [_Tf, ff] 
>         spf <- eElab ("TySpine" :<: (| (TySpine as, [exp _T, exp f]) |))
>         (_Sf, sf) <- eSplit spf
>         [_S, s] <- eLatests [_Sf, sf]
>         (| (PAIR (exp _S) (exp s)) |) 
>       ((SchPi, [_Sf, _Tf]), (elt :~ EA a : es)) -> do
>         _S <- eLatest _Sf
>         sf <- eElab ("s" :<: return (elt :~ ESch a, [exp _S]))
>         [_T, f, s] <- eLatests [_Tf, ff, sf]
>         rf <- eElab ("t" :<: return (SchSpine es,  [  exp _T $$. (s $$ Hd)
>                                                    ,  exp f $$. (s $$ Hd)]))
>         (| exp (eLatest rf) |)
>       ((SchImPi, [_Sf, _Tf]), _) -> do
>         _S <- eLatest _Sf
>         sf <- eHope ("s" :<: return (exp _S))
>         [_T, f, s] <- eLatests [_Tf, ff, sf]
>         rf <- eElab ("t" :<: return (SchSpine es, [exp _T $$. s, exp f $$. s]))
>         (| exp (eLatest rf) |)
>       _ -> eCry [err "elabSpine"]

> instance Problem TySpine where
>   probName x = "elabTySpine"
>   probTel x = ("S", SET) -** \_S -> _S *** ONE
>   probVal x _ = ("S", SET) -** \_S -> _S
>   probElab (TySpine []) [_Sf, sf] = (| PAIR (| exp (eLatest _Sf) |) (| exp (eLatest sf) |)  |)


>   probElab (TySpine (elt :~ EA a : es)) [_Sf, ff] = do
>     (domf, ranf) <- ePi _Sf
>     dom <- eLatest domf
>     argf <- eElab ("arg" :<: return (elt :~ a, [exp dom]))
>     [ran, f, arg] <- eLatests [ranf, ff, argf]
>     rf <- eElab ("appl" :<: return (TySpine es,  [  exp ran $$. (arg $$ Hd)
>                                                  ,  exp f $$. (arg $$ Hd)]))
>     (| exp (eLatest rf) |) 

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

>       (SchPi, [_Sf, _Tf]) -> case a of 
>         ELam (_ :~ Sig [] (_ :~ VarConc (_ :~ x) [] Nothing)) (e :~ t) -> do 
>           [_S, _T] <- eLatests [_Sf, _Tf]
>           ff <- eElab ("eschpi" :<: do  s <- seLambda (x :<: wr (def schElDEF) (exp _S))
>                                         seLambda (x ++ "dub" :<: DUB x (exp _S) (exp s))
>                                         (| (e :~ ESch t, [exp _T $$. s]) |))
>           f <- eLatest ff
>           (| (PAIR (la x $ \a -> nix f :$ (B0 :< A a :< A ZERO :< Hd)) ZERO) |)
>         _ -> error "elabSch - explicit Pi not matched to any lambda"
>       (SchImPi, [_Sf, _Tf]) -> do 
>         [_S, _T] <- eLatests [_Sf, _Tf]
>         ff <- eElab ("eschpi" :<: do  s <- seLambda ("a" :<: exp _S)
>                                       (| (ESch a, [exp _T $$. s]) |))
>         f <- eLatest ff
>         (| (PAIR (la "a" $ \a -> nix f :$ (B0 :< A a :< Hd)) ZERO) |)
>       _ -> error "elabSch - scheme not a scheme"

> instance Problem (EpiSig {k}) where
>   probName x = "EpiSig"
>   probTel x = ONE
>   probVal x es = SCHEME *** ONE
>   probElab (Sig [] (_ :~ VarConc (_ :~ t) [] mety)) [] = do
>     _Sf <- case mety of
>              Just ety -> do 
>                f <- eElab ("varTy" :<: (| (ety, [SET]) |))
>                (| fst (eSplit f) |) 
>              _ -> eHope ("hopeVarTy" :<: (| SET |)) 
>     _S <- eLatest _Sf
>     (| (PAIR (SCHTY (exp _S)) ZERO) |)
>   probElab (Sig [] (_ :~ LetConc (_ :~ t) [] ety)) [] = do
>     _Sf' <- eElab ("letTy" :<: (| (ety, [SET]) |))
>     (_Sf,_) <- eSplit _Sf'
>     _S <- eLatest _Sf
>     (| (PAIR (SCHTY (exp _S)) ZERO) |)
>   probElab (Sig ((sprem :~ VarPrem prem) : prems) (sc :~ VarConc cc ((_ :~ argt) : args) cty)) [] 
>     | concPlate prem == argt = do
>       pf <- eElab ("prem" :<: (| (sprem :~ prem, []) |))
>       (schf,_) <- eSplit pf
>       sch <- eLatest schf
>       sschf <- eElab ("sub" :<: do
>         f <- seLambda (argt :<: wr (def schElDEF) (exp sch))
>         fdub <- seLambda (("dub" ++ argt) :<: DUB argt (exp sch) (exp f))
>         (| (Sig prems (sc :~ VarConc cc args cty), []) |))
>       [sch, ssch] <- eLatests [schf, sschf]
>       (| (PAIR (SCHPI (exp sch) (la argt $ \a -> nix ssch :$ (B0 :< A a :< A ZERO :< Hd))) ZERO) |)
>   probElab (Sig ((sprem :~ VarPrem prem) : prems) (sc :~ LetConc cc ((_ :~ argt) : args) cty)) [] 
>     | concPlate prem == argt = do
>       pf <- eElab ("prem" :<: (| (sprem :~ prem, []) |))
>       (schf,_) <- eSplit pf
>       sch <- eLatest schf
>       sschf <- eElab ("sub" :<: do
>         f <- seLambda (argt :<: wr (def schElDEF) (exp sch))
>         fdub <- seLambda (("dub" ++ argt) :<: DUB argt (exp sch) (exp f))
>         (| (Sig prems (sc :~ LetConc cc args cty), []) |))
>       [sch, ssch] <- eLatests [schf, sschf]
>       (| (PAIR (SCHPI (exp sch) (la argt $ \a -> nix ssch :$ (B0 :< A a :< A ZERO :< Hd))) ZERO) |)
>   probElab x [] = error $ show x

> concPlate :: EpiSig {k} -> Template
> concPlate (Sig _ (_ :~ (VarConc (_ :~ t) _ _))) = t
> concPlate (Sig _ (_ :~ (LetConc (_ :~ t) _ _))) = t
> concPlate (Sig _ (_ :~ (DataConc (_ :~ t) _))) = t


> instance Problem t => Problem (x :~ t) where
>   probName (_ :~ x) = "sourced" ++ probName x
>   probTel (_ :~ x) = probTel x
>   probVal (_ :~ x) = probVal x
>   probElab (_ :~ x) = probElab x


