

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


\subsection{Testing}

> main = do
>     putStrLn $ "Is branches ok? " ++ show testBranches
>     putStrLn $ "Is switch ok? " ++ show testSwitch