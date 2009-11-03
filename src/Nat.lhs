> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Nat where

> import BwdFwd
> import Tm
> import Rules

> natd :: VAL
> natd = ARG (ENUMT (CONSE (TAG "czero") (CONSE (TAG "csuc") NILE))) natc

 natd = ARG (ENUMT (CONSE (TAG "czero") (CONSE (TAG "csuc") NILE))) 
            (L $ H B0 
                  "" 
                  (N (switchOp :@ [CONSE (TAG "czero") 
                                         (CONSE (TAG "csuc") NILE)
                                  ,L $ K DESC
                                  ,PAIR DONE (PAIR (IND UNIT DONE) VOID)
                                  ,NV 0
                                  ])))

> natc :: VAL
> natc = L $ H B0 
>              "" 
>              (N (switchOp :@ [CONSE (TAG "czero") 
>                                     (CONSE (TAG "csuc") NILE)
>                              ,L $ K DESC
>                              ,PAIR DONE (PAIR (IND UNIT DONE) VOID)
>                              ,NV 0
>                              ]))

> nat :: VAL
> nat = MU natd

> zero :: VAL
> zero = INTROS (PAIR ZE VOID)

> suc :: VAL
> suc = L $ H B0 "" (INTROS (PAIR (SU ZE) (PAIR (L $ K (NV 0)) VOID)))

> plus :: VAL -> VAL -> VAL
> plus m n = elimOp @@ [natd
>                      ,L $ K (ARR nat nat)
>                      ,eval [.nat.suc. L $ "" :. [.x.
>                         N $ splitOp :@ [ENUMT (CONSE (TAG "czero") (CONSE (TAG "csuc") NILE)) -- A
>                                        ,L $ "" :. [.t. undefined ]                            -- B
>                                        ,L $ "" :. [.y. undefined ]                            -- C
>                                        ,L $ "" :. [.t. N $ switchOp :@ [CONSE (TAG "czero") (CONSE (TAG "csuc") NILE) -- ls
>                                                                        ,undefined                                     -- f
>                                                                        ,PAIR (L $ K (L $ K (L $ "" :. [.n. NV n ])))  -- T 
>                                                                              (PAIR (L $ K (L $ "" :. [.ih. L $ "" :. [.n.
>                                                                                       N (V suc :$ A (N ((V ih :$ Fst) :$ A VOID :$ A (NV n))))]]))
>                                                                                    VOID)
>                                                                        ,NV t]]                                        -- t
>                                        ,NV x]]                                                -- x
>                            ] $ B0 :< nat :< suc
>                      ,m] $$ A n

> two :: VAL
> two = suc $$ A (suc $$ A zero) 

> four :: VAL
> four = suc $$ A (suc $$ A (suc $$ A (suc $$ A zero)))