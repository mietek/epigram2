

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, PatternGuards #-}

> module Tests.Tactics where

> import BwdFwd
> import Tm
> import Rules

%endif

\subsection{Some machinery}

> fromRight (Right x) = x
> fromRight (Left y) = error $ "fromRight: got a left term: " ++ show y

> isRight (Right _) = True
> isRight _ = False

\subsection{Enum}

branches is supposed to build the following term:

> branchesOpRun t e' p = TIMES (p $$ A ZE) 
>                              (branchesOp @@ [e' , L (H (B0 :< p) 
>                                                      "" (N (V 1 :$ A ((C (Su (N (V 0))))))))])

Let's test it:

> testBranches = equal (typ :>: (fromRight $ withTac, orig)) (B0,3)
>     where t = N (P ([("",0)] := DECL :<: UID))
>           e'= N (P ([("",1)] := DECL :<: ENUMU))
>           p = N (P ([("",2)] := DECL :<: ARR (ENUMT (CONSE t e')) SET))
>           typ = SET
>           withTac = opRun branchesOp [CONSE t e', p]
>           orig = branchesOpRun t e' p

switch is supposed to build the following term:

> switchOpRun t e' p ps n =
>     switchOp @@ [e' 
>                 , L (H (B0 :< p) "" (N (V 1 :$ A ((C (Su (N (V 0))))))))
>                 , ps $$ Snd
>                 , n ]

Let's test it:

> testSwitch = equal (typ :>: (fromRight $ withTac, orig)) (B0,5)
>     where t = N (P ([("",0)] := DECL :<: UID))
>           e'= N (P ([("",1)] := DECL :<: ENUMU))
>           p = N (P ([("",2)] := DECL :<: ARR (ENUMT (CONSE t e')) SET))
>           ps = N (P ([("",3)] := DECL :<: branchesOp @@ [CONSE t e', ARR (ENUMT (CONSE t e')) SET]))
>           n = N (P ([("",4)] := DECL :<: ENUMT (CONSE t e')))
>           typ = SET
>           withTac = opRun switchOp [CONSE t e' , p , ps , SU n]
>           orig = switchOpRun t e' p ps n


\subsection{Desc}

Desc on Arg is supposed to build this term:

> argDescRun x y z = eval [.x.y.z. 
>              SIGMA (NV x) . L $ "" :. [.a.
>              (N (descOp :@ [y $# [a],NV z]))
>              ]] $ B0 :< x :< y :< z

Let's test it:

> testDescArg = equal (typ :>: (fromRight $ withTac, orig)) (B0,3)
>     where x = N (P ([("",0)] := DECL :<: SET))
>           y = N (P ([("",1)] := DECL :<: ARR x DESC))
>           z = N (P ([("",2)] := DECL :<: SET))
>           typ = SET
>           withTac = opRun descOp [ARG x y, z]
>           orig = argDescRun x y z

Ind is supposed to build this term:

> indDescRun x y z = TIMES (ARR x z) (descOp @@ [y,z])

Let's test it:

> testDescInd = equal (typ :>: (fromRight $ withTac, orig)) (B0,3)
>     where x = N (P ([("",0)] := DECL :<: SET))
>           y = N (P ([("",1)] := DECL :<: DESC))
>           z = N (P ([("",2)] := DECL :<: SET))
>           typ = SET
>           withTac = opRun descOp [IND x y, z]
>           orig = indDescRun x y z

Just check that we can use Ind1:

> testDescInd1 = isRight withTac 
>     where x = N (P ([("",1)] := DECL :<: DESC))
>           z = N (P ([("",2)] := DECL :<: SET))
>           typ = SET
>           withTac = opRun descOp [IND1 x, z]


Box on an Arg is supposed to build this term:

> boxArgRun a f d p v = boxOp @@ [f $$ A (v $$ Fst),d,p,v $$ Snd] 

Let's test it:

> testBoxArg = equal (typ :>: (fromRight $ withTac, orig)) (B0,5)
>     where a = N (P ([("",0)] := DECL :<: SET))
>           f = N (P ([("",1)] := DECL :<: ARR a DESC))
>           d = N (P ([("",2)] := DECL :<: SET))
>           p = N (P ([("",3)] := DECL :<: ARR d SET))
>           v = N (P ([("",4)] := DECL :<: descOp @@ [ARG a f, p]))
>           typ = SET
>           withTac = opRun boxOp [ARG a f, d, p, v]
>           orig = boxArgRun a f d p v

Box on an Ind is supposed to build this term:

> boxIndRun h x d p v =
>         eval [.h.x.d.p.v.
>              TIMES (C (Pi (NV h) . L $ "" :. [.y.
>                                    N (V p :$ A (N (V v :$ Fst :$ A (NV y))))]))
>                   (N (boxOp :@ [NV x,NV d,NV p,N (V v :$ Snd)]))
>              ] $ B0 :< h :< x :< d :< p :< v

Let's test it:

> testBoxInd = equal (typ :>: (fromRight $ withTac, orig)) (B0,5)
>     where h = N (P ([("",0)] := DECL :<: SET))
>           x = N (P ([("",1)] := DECL :<: DESC))
>           d = N (P ([("",2)] := DECL :<: SET))
>           p = N (P ([("",3)] := DECL :<: ARR d SET))
>           v = N (P ([("",4)] := DECL :<: descOp @@ [IND h x, p]))
>           typ = SET
>           withTac = opRun boxOp [IND h x, d, p, v]
>           orig = boxIndRun h x d p v

Just check that box does something on Ind1:

> testBoxInd1 = isRight withTac
>     where x = N (P ([("",1)] := DECL :<: DESC))
>           d = N (P ([("",2)] := DECL :<: SET))
>           p = N (P ([("",3)] := DECL :<: ARR d SET))
>           v = N (P ([("",4)] := DECL :<: descOp @@ [IND1 x, p]))
>           typ = SET
>           withTac = opRun boxOp [IND1 x, d, p, v]


Mapbox on an Arg is supposed to build this term:

> mapboxArgRun a f d bp p v =
>   mapBoxOp @@ [f $$ (A (v $$ Fst)),d,bp,p,v $$ Snd]

Let's test it:

> testMapboxArg = equal (typ :>: (fromRight $ withTac, orig)) (B0,6)
>     where a = N (P ([("",0)] := DECL :<: SET))
>           f = N (P ([("",1)] := DECL :<: ARR a DESC))
>           d = N (P ([("",2)] := DECL :<: SET))
>           bpv = N (P ([("",3)] := DECL :<: ARR d SET))
>           p = N (P ([("",4)] := DECL :<: (C (Pi d (eval [.bpv. L $ "" :. 
>                                             [.y. N (V bpv :$ A (NV y))]
>                                            ] $ B0 :< bpv)))))
>           v = N (P ([("",5)] := DECL :<: descOp @@ [ARG a f, d]))
>           typ = boxOp @@ [ARG a f, d, bpv,v]
>           withTac = opRun mapBoxOp [ARG a f, d, bpv, p, v]
>           orig = mapboxArgRun a f d bpv p v

Mapbox on an Ind is supposed to build this term:

> mapboxIndRun h x d bp p v =
>         eval [.h.x.d.bp.p.v.
>              PAIR (L $ "" :. [.y. N (V p :$ A (N (V v :$ Fst :$ A (NV y))))])
>                   (N (mapBoxOp :@ [NV x,NV d
>                                   ,NV bp
>                                   ,NV p
>                                   ,N (V v :$ Snd)
>                                   ]))
>              ] $ B0 :< h :< x :< d :< bp :< p :< v

Test:

> testMapboxInd = equal (typ :>: (fromRight $ withTac, orig)) (B0,6)
>     where h = N (P ([("",0)] := DECL :<: SET))
>           x = N (P ([("",1)] := DECL :<: DESC))
>           d = N (P ([("",2)] := DECL :<: SET))
>           bpv = N (P ([("",3)] := DECL :<: ARR d SET))
>           p = N (P ([("",4)] := DECL :<: (C (Pi d (eval [.bpv. L $ "" :. 
>                                             [.y. N (V bpv :$ A (NV y))]
>                                            ] $ B0 :< bpv)))))
>           v = N (P ([("",5)] := DECL :<: descOp @@ [IND h x, d]))
>           typ = boxOp @@ [IND h x, d, bpv,v]
>           withTac = opRun mapBoxOp [IND h x, d, bpv, p, v]
>           orig = mapboxIndRun h x d bpv p v

Just check that mapBox build something with Ind1:

> testMapboxInd1 = isRight withTac
>     where x = N (P ([("",1)] := DECL :<: DESC))
>           d = N (P ([("",2)] := DECL :<: SET))
>           bpv = N (P ([("",3)] := DECL :<: ARR d SET))
>           p = N (P ([("",4)] := DECL :<: (C (Pi d (eval [.bpv. L $ "" :. 
>                                             [.y. N (V bpv :$ A (NV y))]
>                                            ] $ B0 :< bpv)))))
>           v = N (P ([("",5)] := DECL :<: descOp @@ [IND1 x, d]))
>           typ = boxOp @@ [IND1 x, d, bpv,v]
>           withTac = opRun mapBoxOp [IND1 x, d, bpv, p, v]



elimOp is supposed to build this term:

> elimRun d bp p v =
>          p $$ A v $$ A (mapBoxOp @@ 
>                         [d
>                         ,MU d
>                         ,bp
>                         ,eval [.d.bp.p. L $ "" :. [.x. 
>                               N (elimOp :@ [NV d,NV bp,NV p,NV x])]
>                               ] $ B0 :< d :< bp :< p
>                         ,v])

Let's test now:


> testElim = equal (typ :>: (fromRight $ withTac, orig)) (B0,6)
>     where d = N (P ([("",0)] := DECL :<: DESC))
>           bp = (P ([("",1)] := DECL :<: ARR (MU d) SET))
>           bpv = N bp
>           p = N (P ([("",2)] := DECL :<: (C (Pi (descOp @@ [d,MU d])
>                                              (eval [.d.bp. L $ "" :. [.x. 
>                                               ARR (N (boxOp :@ [NV d,MU (NV d),NV bp,NV x]))
>                                                   (N (V bp :$ A (CON (NV x))))]
>                                                    ] $ B0 :< d :< bpv)))))
>           v = N (P ([("",3)] := DECL :<: (descOp @@ [d, MU d])))
>           typ = N (bp :$ A (MU v))
>           withTac = opRun elimOp [d, bpv, p, CON v]
>           orig = elimRun d bpv p v


\subsection{Equality}

Be green on a Pi:

> eqGreenPiRun s1 t1 f1 s2 t2 f2 = 
>   eval  [.s1.t1.f1.s2.t2.f2.
>         ALL (NV s1) . L $ "" :. [.x1.
>         ALL (NV s2) . L $ "" :. [.x2.
>         IMP (EQBLUE (NV s2 :>: NV x2) (NV s1 :>: NV x1))
>             (eqGreenT (t1 $# [x1] :>: f1 $# [x1]) (t2 $# [x2] :>: f2 $# [x2]))
>         ]]]
>         $ B0 :< s1 :< t1 :< f1 :< s2 :< t2 :< f2

I don't believe it:

> testEqGreenPi = equal (typ :>: (fromRight $ withTac, orig)) (B0,6)
>     where s1 = N (P ([("",0)] := DECL :<: SET))
>           t1 = N (P ([("",1)] := DECL :<: (ARR s1 SET)))
>           f1 = N (P ([("",2)] := DECL :<: (C $ Pi s1 t1)))
>           s2 = N (P ([("",3)] := DECL :<: SET))
>           t2 = N (P ([("",4)] := DECL :<: (ARR s2 SET)))
>           f2 = N (P ([("",5)] := DECL :<: (C $ Pi s2 t2)))
>           typ = PROP
>           withTac = opRun eqGreen [C (Pi s1 t1),f1,C (Pi s2 t2),f2]
>           orig = eqGreenPiRun s1 t1 f1 s2 t2 f2


\subsection{Testing}

> main = do
>     putStrLn $ "Is branches ok? " ++ show testBranches
>     putStrLn $ "Is switch ok? " ++ show testSwitch
>     putStrLn $ "Is desc arg ok? " ++ show testDescArg
>     putStrLn $ "Is desc ind ok? " ++ show testDescInd
>     putStrLn $ "Is desc ind1 ok? " ++ show testDescInd1
>     putStrLn $ "Is box arg ok? " ++ show testBoxArg
>     putStrLn $ "Is box ind ok? " ++ show testBoxInd
>     putStrLn $ "Is box ind1 ok? " ++ show testBoxInd1
>     putStrLn $ "Is mapBox arg ok? " ++ show testMapboxArg
>     putStrLn $ "Is mapBox ind ok? " ++ show testMapboxInd
>     putStrLn $ "Is mapBox ind1 ok? " ++ show testMapboxInd1
>     putStrLn $ "Is elim ok ? " ++ show testElim
>     putStrLn $ "Is eqGreen Pi ok ? " ++ show testEqGreenPi