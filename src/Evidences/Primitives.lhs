

\section{Primitives}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable,
>     FunctionalDependencies, UndecidableInstances #-}

> module Evidences.Primitives where

> import Prelude hiding (foldl, exp, all)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Writer
> import qualified Data.Monoid as M
> import Data.Foldable
> import Data.List hiding (foldl, all)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Evidences.Tm

%endif

> idDEF :: DEF
> idDEF = mkDEF [("PRIM",0),("id",0)] (("S",SET) ->> \_S -> _S --> _S) $
>  eat "S" $ \ _S -> eat "s" $ \ s -> emit s

> uncurryDEF :: DEF
> uncurryDEF = mkDEF 
>   [("PRIM",0),("uncurry",0)]
>   (("S",SET) ->> \_S -> 
>    ("T",_S --> SET) ->> \_T -> 
>    ("C",SET) ->> \_C -> 
>    (("x",_S) ->> \ x -> _T x --> _C) --> 
>    (("x",_S) -** \ x -> _T x) --> _C) $
>   eat "S" $ \ _S -> eat "T" $ \ _T -> eat "C" $ \ _C -> 
>     eat "f" $ \ f -> split $ eat "s" $ \ s -> eat "t" $ \ t ->
>     emit (f s t)

> zeroElimDEF :: DEF
> zeroElimDEF = mkDEF
>   [("PRIM",0),("zeroElim",0)]
>   (ZERO --> (("S",SET) ->> \_S -> _S))
>   (cases [])

> inhElimDEF :: DEF
> inhElimDEF = mkDEF
>   [("PRIM",0),("inhElim",0)]
>   (("T",SET) ->> \_T ->
>    ("p",PRF (INH _T)) ->> \p ->
>    ("P",PRF (INH _T) --> PROP) ->> \_P ->
>    ("m",(("t",_T) ->> \t -> PRF (_P (WIT t)))) ->> \m ->
>    PRF (_P p)) $
>   eat "T" $ \_T ->
>    cases [(Wit , eat "t" $ \t -> eat "P" $ \_P -> eat "m" $ \m -> 
>             emit (m t))]

> branchesDEF :: DEF
> branchesDEF = mkDEF
>   [("PRIM",0),("branches",0)]
>   (("E",ENUMU) ->> \_E ->
>    ("P",ARR (ENUMT _E) SET) ->> \_P ->
>    SET)
>   branchesOP
>     where 
>      branchesOP = cases  
>       [  (NilE , eat "P" $ \_P -> emit ONE)
>       ,  (ConsE , eat "T" $ \_T -> eat "E" $ \_E -> eat "P" $ \_P -> emit $
>                     TIMES (_P $$. ZE) 
>                       (wr (D branchesDEF S0 (branchesOP 0)) 
>                           _E (la "n" $ \n -> wr _P (SU n))) )]

> switchDEF :: DEF
> switchDEF = mkDEF
>   [("PRIM",0),("switch",0)]
>   (("E",ENUMU) ->> \_E ->
>    ("x",ENUMT _E) ->> \x ->
>    ("P",ARR (ENUMT _E) SET) ->> \_P ->
>    ("b",wr (D branchesDEF S0 (defOp branchesDEF)) _E _P) ->> \b -> 
>    _P x)
>   switchOP
>     where
>      switchOP = cases  
>        [  (NilE , cases [])
>        ,  (ConsE , eat "T" $ \_T -> eat "E" $ \_E -> cases 
>             [  (Ze , eat "P" $ \_P -> eat "b" $ \b -> emit (b $$ Hd))
>             ,  (Su , eat "x" $ \x -> eat "P" $ \_P -> eat "b" $ \b ->
>                        emit (wr (D switchDEF S0 (switchOP 0)) 
>                                   _E x _P (b $$ Tl)))  ]) ]

> tabulateDEF :: DEF
> tabulateDEF = mkDEF
>   [("PRIM",0),("tabulate",0)]
>   (("E",ENUMU) ->> \_E ->
>    ("P",ARR (ENUMT _E) SET) ->> \_P ->
>    ("f",("e", ENUMT _E) ->> \e -> _P e) ->> \f ->
>    wr (def branchesDEF) _E _P)
>   tabulateOP
>     where
>       tabulateOP = cases
>         [  (NilE , eat "P" $ \_P -> eat "f" $ \f -> emit ZERO)
>         ,  (ConsE , eat "x" $ \x -> eat "E" $ \_E -> eat "P" $ \_P -> eat "f" $ \f -> 
>              emit $ PAIR (f ZE) (wr (def tabulateDEF) _E (la "e" $ \e -> wr _P (SU e)) (la "e" $ \e -> wr f (SU e)))) 
>         ] 
>   

> iDescDEF :: DEF
> iDescDEF = mkDEF
>   [("PRIM",0),("IDesc",0)]
>   (("I",SET) ->> \_ -> SET) $
>   eat "I" $ \_I -> emit $ IMU ONE (wr (def iDescDDEF) _I) ZERO

> iDescDDEF :: DEF
> iDescDDEF = mkDEF
>   [("PRIM",0),("IDescD",0)]
>   (("I",SET) ->> \_ -> ONE --> wr (def iDescDEF) ONE) $
>   eat "I" $ \_I -> eat "_" $ \_ -> emit $ IFSIGMA 
>    (CONSE (TAG "varD") 
>     (CONSE (TAG "constD")
>      (CONSE (TAG "piD")
>       (CONSE (TAG "fpiD")
>        (CONSE (TAG "sigmaD")
>         (CONSE (TAG "fsigmaD")
>          (CONSE (TAG "prodD")  
>           NILE)))))))
>    {- varD: -}    (PAIR (ISIGMA _I (LK $ ICONST ONE))
>    {- constD: -}  (PAIR (ISIGMA SET (LK $ ICONST ONE))
>    {- piD: -}     (PAIR (ISIGMA SET (la "S" $ \_S -> 
>                     (IPROD (TAG "T") (IPI _S (LK $ IVAR ZERO)) 
>                            (ICONST ONE))))
>    {- fpiD: -}    (PAIR (ISIGMA ENUMU (la "E" $ \_E ->
>                     (IPROD (TAG "T") (IPI (ENUMT _E) (LK $ IVAR ZERO))
>                            (ICONST ONE))))
>    {- sigmaD: -}  (PAIR (ISIGMA SET (la "S" $ \_S ->  
>                     (IPROD (TAG "T") (IPI _S (LK $ IVAR ZERO)) 
>                            (ICONST ONE))))
>    {- fsigmaD: -} (PAIR (ISIGMA ENUMU (la "E" $ \_E ->
>                     (IPROD (TAG "T") (IFPI _E (LK $ IVAR ZERO))
>                            (ICONST ONE))))
>    {- prodD: -}   (PAIR (ISIGMA UID (la "u" $ \_ -> 
>                          (IPROD (TAG "C") (IVAR ZERO) 
>                           (IPROD (TAG "D") (IVAR ZERO) (ICONST ONE)))))
>                     ZERO))))))) 

> idescDEF :: DEF
> idescDEF = mkDEF
>   [("PRIM",0),("idesc",0)]
>   (("I", SET) ->> \_I ->
>    ("D", wr (def iDescDEF) _I) ->> \_D ->
>    ("X", ARR _I SET) ->> \_X -> SET)
>    idescOP
>      where 
>       idescOP = eat "I" $ \_I -> cases [ (Con , split $ cases 
>        [  (Ze {- IVar -}, 
>                 speat "i" $ \i -> eat "_" $ \_ -> eat "X" $ \_X -> emit $ _X i) 
>        ,  (Su , cases 
>         [  (Ze {- IConst -}, 
>                  speat "K" $ \_K -> eat "_" $ \_ -> eat "X" $ \_X -> emit _K)
>         ,  (Su , cases
>          [  (Ze {- IPi -}, 
>                  speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                  emit $ PI _S (la "s" $ \s ->
>                            wr (def idescDEF) (wr _I)  
>                                              (wr _D s) (wr _X)))
>          ,  (Su , cases
>           [  (Ze {- IFPi -}, 
>                   speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                   emit $ wr (def branchesDEF) _E (la "s" $ \s -> 
>                            wr (def idescDEF) (wr _I) 
>                                              (wr _D s) (wr _X)))
>           ,  (Su , cases
>            [  (Ze {- ISigma -}, 
>                     speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                     emit $ SIGMA _S (la "s" $ \s -> 
>                               wr (def idescDEF) (wr _I) 
>                                                 (wr _D s) (wr _X))) 
>            ,  (Su , cases
>             [  (Ze {- IFSigma -}, 
>                      speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                      emit $ SIGMA (ENUMT _E) (la "e" $ \e -> 
>                               wr (def idescDEF) (wr _I)  
>                                     (wr (def switchDEF) (wr _E) e
>                                            (LK (wr (def iDescDEF) (wr _I) ZERO)) (wr _D))
>                                     (wr _X)))
>             ,  (Su , cases
>              [  (Ze {- IProd -}, 
>                    speat "u" $ \_ -> speat "C" $ \_C -> 
>                      speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X ->
>                    emit $ TIMES  (wr (def idescDEF) _I _C _X) 
>                                  (wr (def idescDEF) _I _D _X))
>        ])])])])])])])]

> iAllDEF :: DEF
> iAllDEF = mkDEF
>   [("PRIM",0),("All",0)]
>   (("I", SET) ->> \_I ->
>    ("D", wr (def iDescDEF) _I) ->> \_D ->
>    ("X", ARR _I SET) ->> \_X -> 
>    ("t", wr (def idescDEF) _I _D _X) ->> \t ->
>    wr (def iDescDEF) (("i", _I) -** \i -> _X i))  
>   iAllOP
>      where 
>       iAllOP = eat "I" $ \_I -> cases [ (Con , split $ cases 
>        [  (Ze {- IVar -}, 
>                 speat "i" $ \i -> eat "_" $ \_ -> eat "X" $ \_X -> eat "x" $ \x -> emit (IVAR (PAIR i x))) 
>        ,  (Su , cases 
>         [  (Ze {- IConst -}, 
>                  speat "K" $ \_K -> eat "_" $ \_ -> eat "X" $ \_X -> eat "k" $ \k -> emit (ICONST ONE))
>         ,  (Su , cases
>          [  (Ze {- IPi -}, 
>                  speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> eat "f" $ \f -> 
>                  emit $ IPI _S (la "s" $ \s -> 
>                            wr (def iAllDEF) (wr _I) (wr _D s) 
>                                             (wr _X) (wr f s)))
>          ,  (Su , cases
>           [  (Ze {- IFPi -}, 
>                   speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> eat "t" $ \t -> 
>                   emit $ IFPI _E (la "e" $ \e ->
>                            wr (def iAllDEF) (wr _I) (wr _D e) (wr _X)
>                                      (wr (def switchDEF) (wr _E) e 
>                                                 (la "f" $ \f -> 
>                                                    wr (def idescDEF) (wr _I) (wr _D f) (wr _X)) (wr t))))
>           ,  (Su , cases
>            [  (Ze {- ISigma -}, 
>                     speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                     speat "s" $ \s -> eat "t" $ \t ->  
>                     emit $ wr (def iAllDEF) _I (_D s) _X t) 
>            ,  (Su , cases
>             [  (Ze {- IFSigma -}, 
>                      speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X ->
>                      speat "e" $ \e -> eat "t" $ \t -> 
>                      emit $ wr (def iAllDEF) _I  
>                                       (wr (def switchDEF) _E 
>                                              (LK (wr (def iDescDEF) _I ZERO)) _D)
>                                       _X t)
>             ,  (Su , cases
>              [  (Ze {- IProd -}, 
>                    speat "u" $ \u -> speat "C" $ \_C -> speat "D" $ \_D -> eat "_" $ \_ -> 
>                    eat "X" $ \_X -> speat "c" $ \c -> eat "d" $ \d ->
>                    emit $ IPROD (wr (TAG "h")) -- can we make a better name choice here please?
>                                 (wr (def iAllDEF) _I _C _X c) 
>                                 (wr (def iAllDEF) _I _D _X d))
>        ])])])])])])])]  

> iallDEF :: DEF
> iallDEF = mkDEF
>   [("PRIM",0),("all",0)]
>   (("I", SET) ->> \_I ->
>    ("D", wr (def iDescDEF) _I) ->> \_D ->
>    ("X", ARR _I SET) ->> \_X ->
>    ("P", ARR (("i", _I) -** \i -> _X i) SET) ->> \_P ->
>    ("p", ("x", ("i", _I) -** \i -> _X i) ->> \x -> _P x) ->> \p -> 
>    ("t", wr (def idescDEF) _I _D _X) ->> \t ->
>    wr (def iDescDEF) (("i", _I) -** \i -> _X i))  
>   iallOP
>      where 
>       iallOP = eat "I" $ \_I -> cases [ (Con , split $ cases 
>        [  (Ze {- IVar -}, 
>                 speat "i" $ \i -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                 eat "P" $ \_P -> eat "p" $ \p -> eat "x" $ \x -> emit (p (PAIR i x))) 
>        ,  (Su , cases 
>         [  (Ze {- IConst -}, 
>                  speat "K" $ \_K -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                  eat "P" $ \_P -> eat "p" $ \p -> eat "k" $ \k -> emit ZERO)
>         ,  (Su , cases
>          [  (Ze {- IPi -}, 
>                  speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                  eat "P" $ \_P -> eat "p" $ \p -> eat "f" $ \f -> 
>                  emit $ (la "s" $ \s ->
>                            wr (def iallDEF) (wr _I) (wr _D s) (wr _X) 
>                                             (wr _P) (wr p) (wr f s)))
>          ,  (Su , cases
>           [  (Ze {- IFPi -}, 
>                   speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                   eat "P" $ \_P -> eat "p" $ \p -> eat "t" $ \t -> 
>                   emit $ wr (def tabulateDEF) _E (la "e" $ \e -> wr (def idescDEF) (("i", wr _I) -** \i -> wr _X i) (wr _P) 
>                            (wr (def iAllDEF) (wr _I) (wr _D e) (wr _X)
>                                      (wr (def switchDEF) (wr _E) e 
>                                                 (la "f" $ \f ->
>                                                    wr (def idescDEF) (wr _I) (wr _D f) (wr _X)) (wr t))))
>                                    (la "e" $ \e -> (wr (def iAllDEF) (wr _I) (wr _D e) (wr _X) (wr _P) (wr p)
>                                                  (wr (def switchDEF) (wr _E) e
>                                                             (la "f" $ \f ->
>                                                                wr (def idescDEF) (wr _I) (wr _D f) (wr _X)) (wr t))))) 
>           ,  (Su , cases
>            [  (Ze {- ISigma -}, 
>                     speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                     eat "P" $ \_P -> eat "p" $ \p -> speat "s" $ \s -> eat "t" $ \t ->  
>                     emit $ wr (def iallDEF) _I (_D s) _X _P p t) 
>            ,  (Su , cases
>             [  (Ze {- IFSigma -}, 
>                      speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X ->
>                      eat "P" $ \_P -> eat "p" $ \p -> speat "e" $ \e -> eat "t" $ \t -> 
>                      emit $ wr (def iallDEF) _I  
>                                       (wr (def switchDEF) _E 
>                                              (LK (wr (def iDescDEF) _I ZERO)) _D)
>                                       _X _P p t)
>             ,  (Su , cases
>              [  (Ze {- IProd -}, 
>                    speat "u" $ \u -> speat "C" $ \_C -> speat "D" $ \_D -> eat "_" $ \_ -> 
>                    eat "X" $ \_X -> eat "P" $ \_P -> eat "p" $ \p -> speat "c" $ \c -> eat "d" $ \d ->
>                    emit $ PAIR  (wr (def iallDEF) _I _C _X _P p c) 
>                                 (wr (def iallDEF) _I _D _X _P p d))
>        ])])])])])])])] 

> iinductionDEF :: DEF
> iinductionDEF = mkDEF
>   [("PRIM",0),("induction",0)]
>   (("I", SET) ->> \_I ->
>    ("D", ARR _I (wr (def iDescDEF) _I)) ->> \_D -> 
>    ("ix", ("i", _I) -** \i -> IMU _I _D i) ->> \ix -> 
>    ("P", ARR (("i'", _I) -** \i' -> IMU _I _D i') SET) ->> \_P -> 
>    ("p", ("i'", _I) ->> \i' -> 
>          ("x'", wr (def idescDEF) _I (_D i') (la "i'" $ \i' -> IMU _I _D i')) ->> \x' -> 
>          ("xh", wr (def idescDEF) (("i'", _I) -** \i' -> IMU _I _D i') 
>                           (wr (def iAllDEF) _I (_D i') (la "i'" $ \i' -> IMU _I _D i') x') _P) ->> \xh -> 
>          _P (PAIR i' (CON x'))) ->> \p -> 
>    _P ix)
>   iinductionOP
>     where
>       iinductionOP = eat "I" $ \_I -> eat "D" $ \_D -> speat "i" $ \i -> cases 
>         [ (Con , speat "x" $ \x -> eat "_" $ \_ -> eat "P" $ \_P -> eat "p" $ \ p -> emit $
>                  p i x (wr (def iallDEF) _I (_D i) (la "i'" $ \i' -> IMU (wr _I) (wr _D) i') _P
>                                   (la "ix" $ \ix -> wr (def iinductionDEF) (wr _I) (wr _D) ix (wr _P) (wr p)) x)) ] 

> prims :: [ DEF ] 
> prims = [  idDEF , uncurryDEF , zeroElimDEF , inhElimDEF  
>         ,  branchesDEF , switchDEF , iDescDDEF , iDescDEF , idescDEF 
>         ,  iAllDEF ]
