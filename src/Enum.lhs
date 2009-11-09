\section{Enum}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Enum where

%endif

> import -> CanConstructors where
>   EnumU  :: Can t
>   EnumT  :: t -> Can t
>   NilE   :: Can t
>   ConsE  :: t -> t -> Can t
>   Ze     :: Can t
>   Su     :: t -> Can t 

> import -> CanPats where
>   pattern ENUMU      = C EnumU 
>   pattern ENUMT e    = C (EnumT e) 
>   pattern NILE        = C NilE
>   pattern CONSE t e  = C (ConsE t e) 
>   pattern ZE         = C Ze
>   pattern SU n       = C (Su n)

> import -> CanCompile where
>   makeBody Ze = CTag 0
>   makeBody (Su x) = STag (makeBody x)

> import -> TraverseCan where
>   traverse f EnumU        = (|EnumU|)
>   traverse f (EnumT e)    = (|EnumT (f e)|)
>   traverse f NilE         = (|NilE|)
>   traverse f (ConsE t e)  = (|ConsE (f t) (f e)|)
>   traverse f Ze           = (|Ze|)
>   traverse f (Su n)       = (|Su (f n)|) 

> import -> CanTyRules where
>   canTy ev (Set :>: EnumU)    = return EnumU
>   canTy eval (Set :>: EnumT e)  = do
>     ev <- eval e 
>     return $ EnumT (ENUMU :>: e)
>   canTy ev (EnumU :>: NilE)       = return NilE
>   canTy eval (EnumU :>: ConsE t e)  = do
>     tv <- eval t
>     ev <- eval e
>     return $ ConsE (UID :>: t) (ENUMU :>: e)
>   canTy ev (EnumT (CONSE t e) :>: Ze)    = return Ze 
>   canTy ev (EnumT (CONSE t e) :>: Su n)  = do
>     nv <- ev n
>     return $ Su (ENUMT e :>: n)

> import -> OpCode where
>   branchesOp = Op 
>     { opName   = "Branches"
>     , opArity  = 2 
>     , opTy     = bOpTy
>     , opRun    = bOpRun
>     } where
>         bOpTy chev [e , p] = do
>                  (e :=>: ev) <- chev (ENUMU :>: e)
>                  (p :=>: pv) <- chev (ARR (ENUMT ev) SET :>: p)
>                  return ([ e :=>: ev
>                          , p :=>: pv]
>                          , SET)
>         bOpTy _ _ = mzero
>         bOpRun :: [VAL] -> Either NEU VAL
>         bOpRun [NILE , p] = Right UNIT
>         bOpRun [CONSE t e' , p] = Right $ trustMe (typeBranches :>: tacBranches) $$ A t $$ A e' $$ A p
>         bOpRun [N e , _] = Left e 
>         typeBranches = C (Pi ENUMU (L (H B0 "" (ARR (ARR (ENUMT $ NV 0) SET) SET))))
>         tacBranches = lambda 
>                        (\t -> 
>                         lambda 
>                         (\e' -> 
>                          lambda 
>                           (\p -> 
>                            timesTac (use p . apply (can Ze) $ done)
>                                     (useOp branchesOp [use e' done, 
>                                                        lambda
>                                                        (\x -> 
>                                                         use p . apply (use x done) $ done)] 
>                                      done))))

tacBranches is supposed to build the following term:

<           (TIMES (p $$ A ZE) 
<                 (branchesOp @@ [e' , L (H (B0 :< p) 
<                                  "" (N (V 1 :$ A ((C (Su (N (V 0))))))))]))


>   switchOp = Op
>     { opName = "Switch"
>     , opArity = 4
>     , opTy = sOpTy
>     , opRun = sOpRun
>     } where
>         sOpTy chev [e , p , b, x] = do
>           (e :=>: ev) <- chev (ENUMU :>: e)
>           (p :=>: pv) <- chev (ARR (ENUMT ev) SET :>: p)
>           (b :=>: bv) <- chev (branchesOp @@ [ev , pv] :>: b)
>           (x :=>: xv) <- chev (ENUMT ev :>: x)
>           return $ ([ e :=>: ev
>                     , p :=>: pv
>                     , b :=>: bv
>                     , x :=>: xv ] 
>                    , pv $$ A xv)
>         sOpRun :: [VAL] -> Either NEU VAL
>         sOpRun [CONSE t e' , p , ps , ZE] = Right $ ps $$ Fst
>         sOpRun [CONSE t e' , p , ps , SU n] = Right $
>           switchOp @@ [e' 
>                       , L (H (B0 :< p) "" (N (V 1 :$ A ((C (Su (N (V 0))))))))
>                       , ps $$ Snd
>                       , n ]
>         sOpRun [_ , _ , _ , N n] = Left n


> import -> Operators where
>   branchesOp :
>   switchOp :

> import -> OpCompile where
>     ("Branches", _) -> Ignore
>     ("Switch", [e, p, b, x]) -> App (Var "switch") [b, x]
