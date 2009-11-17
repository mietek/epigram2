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
>   pattern NILE       = C NilE
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
>   canTy _ (Set :>: EnumU)    = return EnumU
>   canTy chev (Set :>: EnumT e)  = do
>     eev@(e :=>: ev) <- chev (ENUMU :>: e)
>     return $ EnumT eev
>   canTy chev (EnumU :>: NilE)       = return NilE
>   canTy chev (EnumU :>: ConsE t e)  = do
>     ttv@(t :=>: tv) <- chev (UID :>: t)
>     eev@(e :=>: ev) <- chev (ENUMU :>: e)
>     return $ ConsE ttv eev
>   canTy _ (EnumT (CONSE t e) :>: Ze)    = return Ze 
>   canTy chev (EnumT (CONSE t e) :>: Su n)  = do
>     nnv@(n :=>: nv) <- chev (ENUMT e :>: n)
>     return $ Su nnv

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
>         bOpTy _ _ = traceErr "branches: invalid arguments"
>         bOpRun :: [VAL] -> Either NEU VAL
>         bOpRun [NILE , _] = Right UNIT
>         bOpRun [CONSE t e' , p] = Right $ trustMe (typeBranches :>: tacBranches) $$ A t $$ A e' $$ A p
>         bOpRun [N e , _] = Left e 
>         typeBranches = trustMe (SET :>: tacTypeBranches)
>         tacTypeBranches = can $ Pi (can UId)
>                                    (lambda (\t ->
>                                     can $ Pi (can EnumU)
>                                              (lambda (\e ->
>                                               arrTac (arrTac (can $ EnumT (can $ ConsE (use t done)
>                                                                                          (use e done)))
>                                                                (can Set))
>                                                      (can Set)))))
>         tacBranches = lambda $ \t ->
>                       lambda $ \e' ->
>                       lambda $ \p ->
>                       timesTac (use p . apply (A (can Ze)) $ done)
>                                (useOp branchesOp [ use e' done
>                                                  , lambda $ \x -> 
>                                                    use p . apply (A (can (Su (use x done)))) $ done] 
>                                 done)

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
>         sOpRun [CONSE t e' , p , ps , SU n] = Right $ trustMe (typeSwitch :>: tacSwitch) 
>                                                       $$ A t $$ A e' $$ A p $$ A ps $$ A n
>         sOpRun [_ , _ , _ , N n] = Left n

>         tacSwitch = lambda $ \t ->
>                     lambda $ \e' ->
>                     lambda $ \p ->
>                     lambda $ \ps ->
>                     lambda $ \n ->
>                     useOp switchOp [ use e' done
>                                    , lambda $ \x -> 
>                                      use p . apply (A (can (Su (use x done)))) $ done
>                                    , use ps . apply Snd $ done
>                                    , use n done ]
>                     done
>         typeSwitch = trustMe (SET :>: tacTypeSwitch) 
>         tacTypeSwitch = can $ Pi (can UId)
>                               (lambda (\t ->
>                                 can $ Pi (can EnumU)
>                                          (lambda (\e -> 
>                                           can $ Pi (arrTac (can $ EnumT (can $ ConsE (use t done) (use e done)))
>                                                            (can Set))
>                                                    (lambda (\p ->
>                                                     arrTac (useOp branchesOp [ can $ ConsE (use t done) (use e done)
>                                                                                 , use p done]
>                                                             done)
>                                                             (can $ Pi (can $ EnumT (use e done))
>                                                                         (lambda (\x -> 
>                                                                          use p . apply (A $ can $ Su $ use x done) $ done)))))))))


> import -> Operators where
>   branchesOp :
>   switchOp :

> import -> OpCompile where
>     ("Branches", _) -> Ignore
>     ("Switch", [e, p, b, x]) -> App (Var "switch") [b, x]

> import -> OpRunEqGreen where
>   opRunEqGreen [ENUMU,NILE,ENUMU,NILE] = Right $ TRIVIAL
>   opRunEqGreen [ENUMU,CONSE t1 e1,ENUMU,CONSE t2 e2] = Right $ 
>     eval [.t1.e1.t2.e2. C (And (eqGreenT (UID :>: NV t1) (UID :>: NV t2))
>                                (eqGreenT (ENUMU :>: NV e1) (ENUMU :>: NV e2)))
>          ] $ B0 :< t1 :< e1 :< t2 :< e2
>   opRunEqGreen [ENUMT (CONSE _ e1),ZE,ENUMT (CONSE _ e2),ZE] = Right TRIVIAL
>   opRunEqGreen [ENUMT (CONSE _ e1),SU n1,ENUMT (CONSE _ e2),SU n2] = Right $ 
>     eval [.e1.n1.e2.n2. eqGreenT (ENUMT (NV e1) :>: NV n1) 
>                                  (ENUMT (NV e2) :>: NV n2) 
>          ] $ B0 :< e1 :< n1 :< e2 :< n2
