

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

> falseElimDEF :: DEF
> falseElimDEF = mkDEF
>   [("PRIM",0),("falseElim",0)]
>   (PRF ZERO --> (("S",SET) ->> \_S -> _S))
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
>       ,  (ConsE , eat "u" $ \_ -> eat "E" $ \_E -> eat "P" $ \_P -> emit $
>                     TIMES (_P ZE) 
>                       (wr (def branchesDEF) 
>                           _E (la "n" $ \n -> wr _P (SU n))) )]

> switchDEF :: DEF
> switchDEF = mkDEF
>   [("PRIM",0),("switch",0)]
>   (("E",ENUMU) ->> \_E ->
>    ("x",ENUMT _E) ->> \x ->
>    ("P",ARR (ENUMT _E) SET) ->> \_P ->
>    ("b",wr (def branchesDEF) _E _P) ->> \b -> 
>    _P x)
>   switchOP
>     where
>      switchOP = cases  
>        [  (NilE , cases [])
>        ,  (ConsE , eat "u" $ \_ -> eat "E" $ \_E -> cases 
>             [  (Ze , eat "P" $ \_P -> split $ eat "b" $ \b -> eat "bs" $ \bs -> emit b)
>             ,  (Su , eat "x" $ \x -> eat "P" $ \_P -> split $ eat "b" $ \b -> eat "bs" $ \bs ->
>                        emit (wr (def switchDEF) _E x (la "n" $ \n -> wr _P (SU n)) bs))  ]) ]

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
>   [("PRIM",0),("Desc",0)]
>   (("I",SET) ->> \_ -> SET) $
>   eat "I" $ \_I -> emit $ IMU ONE (wr (def iDescDDEF) _I) ZERO

> iDescDDEF :: DEF
> iDescDDEF = mkDEF
>   [("PRIM",0),("DescD",0)]
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
>    {- prodD: -}   (PAIR (ISIGMA UID (LK   
>                          (IPROD (TAG "C") (IVAR ZERO) 
>                           (IPROD (TAG "D") (IVAR ZERO) (ICONST ONE)))))
>                     ZERO))))))) 

> idescDEF :: DEF
> idescDEF = mkDEF
>   [("PRIM",0),("desc",0)]
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
>                            wr (def idescDEF) (wr _I) (wr _D s) (wr _X)))
>          ,  (Su , cases
>           [  (Ze {- IFPi -}, 
>                   speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                   emit $ wr (def branchesDEF) _E (la "s" $ \s -> 
>                            wr (def idescDEF) (wr _I) (wr _D s) (wr _X)))
>           ,  (Su , cases
>            [  (Ze {- ISigma -}, 
>                     speat "S" $ \_S -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                     emit $ SIGMA _S (la "s" $ \s -> 
>                               wr (def idescDEF) (wr _I) (wr _D s) (wr _X))) 
>            ,  (Su , cases
>             [  (Ze {- IFSigma -}, 
>                      speat "E" $ \_E -> speat "D" $ \_D -> eat "_" $ \_ -> eat "X" $ \_X -> 
>                      emit $ SIGMA (ENUMT _E) (la "e" $ \e -> 
>                               wr (def idescDEF) (wr _I)  
>                                     (wr (def switchDEF) (wr _E) e
>                                            (LK (wr (def iDescDEF) (wr _I))) (wr _D))
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
>                            wr (def iAllDEF) (wr _I) (wr _D s) (wr _X) (wr f s)))
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
>                                       (wr (def switchDEF) _E e 
>                                              (LK (wr (def iDescDEF) _I)) _D)
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
>                                       (wr (def switchDEF) _E e 
>                                              (LK $ wr (def iDescDEF) (wr _I) ZERO) _D)
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
>    ("i",  _I) ->> \i ->
>    ("x", IMU _I _D i) ->> \x -> 
>    ("P", ARR (("i'", _I) -** \i' -> IMU _I _D i') SET) ->> \_P -> 
>    ("p", ("i'", _I) ->> \i' -> 
>          ("x'", wr (def idescDEF) _I (_D i') (la "i'" $ \i' -> IMU _I _D i')) ->> \x' -> 
>          ("xh", wr (def idescDEF) (("i'", _I) -** \i' -> IMU _I _D i') 
>                           (wr (def iAllDEF) _I (_D i') (la "i'" $ \i' -> IMU _I _D i') x') _P) ->> \xh -> 
>          _P (PAIR i' (CON x'))) ->> \p -> 
>    _P (PAIR i x))
>   iinductionOP
>     where
>       iinductionOP = eat "I" $ \_I -> eat "D" $ \_D -> eat "i" $ \i -> cases 
>         [ (Con , eat "x" $ \x -> eat "P" $ \_P -> eat "p" $ \ p -> emit $
>                  p i x (wr (def iallDEF) _I (_D i) (la "i'" $ \i' -> IMU (wr _I) (wr _D) i') _P
>                                   (la "ix" $ \ix -> wr (def iinductionDEF) (wr _I) (wr _D) ix (wr _P) (wr p)) x)) ] 

> tindDEF :: DEF
> tindDEF = mkDEF 
>   [("PRIM",0),("tind",0)]
>   (("I", SET) ->> \_I ->
>    ("Cs", ENUMU) ->> \_Cs ->
>    ("Ds", ARR _I (wr (def branchesDEF) _Cs (LK $ wr (def iDescDEF) _I))) ->> \_Ds ->
>    ("i", _I) ->> \i -> 
>    ("x", IMU _I (la "i'" $ \i' -> IFSIGMA _Cs (_Ds i')) i) ->> \x -> 
>    ("P", ARR (("i'", _I) -** \i' -> 
>               IMU _I (la "i''" $ \i'' -> IFSIGMA _Cs (_Ds i'')) i') SET) ->> \_P ->
>    ("m", wr (def branchesDEF) _Cs (la "c" $ \c ->
>       ("i'", _I) ->> \i' ->
>       ("xs", wr (def idescDEF) _I 
>                (wr (def switchDEF) _Cs c (LK $ wr (def iDescDEF) _I) (_Ds i'))
>                (la "i''" $ \i'' -> IMU _I (la "i'''" $ \i''' -> IFSIGMA _Cs (_Ds i''')) i'')) ->> \xs ->
>       ("hs", wr (def idescDEF) (("i''", _I) -** \i'' -> IMU _I (la "i'''" $ \i''' -> IFSIGMA _Cs (_Ds i''')) i'')
>                (wr (def iAllDEF) _I 
>                   (wr (def switchDEF) _Cs c (LK $ wr (def iDescDEF) _I) (_Ds i'))
>                   (la "i''" $ \i'' -> IMU _I (la "i'''" $ \i''' -> IFSIGMA _Cs (_Ds i''')) i'') xs) _P) ->> \_ ->
>       _P (PAIR i' (CON (PAIR c xs))))) ->> \m ->
>    _P (PAIR i x))
>   tindOP
>     where
>       tindOP = 
>         eat "_I" $ \_I -> 
>         eat "Cs" $ \_Cs -> 
>         eat "Ds" $ \_Ds -> 
>         eat "i" $ \i -> 
>         eat "x" $ \x -> 
>         eat "P" $ \_P -> 
>         eat "m" $ \m ->
>         emit $ wr (def iinductionDEF) _I (la "i'" $ \i' -> IFSIGMA (wr _Cs) (wr _Ds i')) i x _P
>                  (la "j" $ \j -> la "y" $ \y -> la "yh" $ \yh ->
>                   wr (def switchDEF) (wr _Cs) (V (Fs Fz) :$ (B0 :< Hd)) (la "c" $ \c ->
>                     ("i'", wr _I) ->> \i' ->
>                     ("xs", wr (def idescDEF) (wr _I) 
>                       (wr (def switchDEF) (wr _Cs) c (LK $ wr (def iDescDEF) (wr _I)) (wr _Ds i'))
>                       (la "i''" $ \i'' -> IMU (wr _I) (la "i'''" $ \i''' -> IFSIGMA (wr _Cs) (wr _Ds i''')) i'')) ->> \xs ->
>                     ("hs", wr (def idescDEF) (("i''", wr _I) -** \i'' -> IMU (wr _I) (la "i'''" $ \i''' -> IFSIGMA (wr _Cs) (wr _Ds i''')) i'')
>                       (wr (def iAllDEF) (wr _I) 
>                         (wr (def switchDEF) (wr _Cs) c (LK $ wr (def iDescDEF) (wr _I)) (wr _Ds i'))
>                         (la "i''" $ \i'' -> IMU (wr _I) (la "i'''" $ \i''' -> IFSIGMA (wr _Cs) (wr _Ds i''')) i'') xs) (wr _P)) ->> \_ ->
>                     wr _P (PAIR i' (CON (PAIR c xs))))
>                    (wr m) j (V (Fs Fz) :$ (B0 :< Tl)) yh)

> tcaseDEF :: DEF
> tcaseDEF = mkDEF 
>   [("PRIM",0),("tcase",0)]
>   (("I", SET) ->> \_I ->
>    ("Cs", ENUMU) ->> \_Cs ->
>    ("Ds", ARR _I (wr (def branchesDEF) _Cs (LK $ wr (def iDescDEF) _I))) ->> \_Ds ->
>    ("i", _I) ->> \i -> 
>    ("x", IMU _I (la "i'" $ \i' -> IFSIGMA _Cs (_Ds i')) i) ->> \x -> 
>    ("P", ARR (("i'", _I) -** \i' -> 
>               IMU _I (la "i''" $ \i'' -> IFSIGMA _Cs (_Ds i'')) i') SET) ->> \_P ->
>    ("m", wr (def branchesDEF) _Cs (la "c" $ \c ->
>       ("i'", _I) ->> \i' ->
>       ("xs", wr (def idescDEF) _I 
>                (wr (def switchDEF) _Cs c (LK $ wr (def iDescDEF) _I) (_Ds i'))
>                (la "i''" $ \i'' -> IMU _I (la "i'''" $ \i''' -> IFSIGMA _Cs (_Ds i''')) i'')) ->> \xs ->
>       _P (PAIR i' (CON (PAIR c xs))))) ->> \m ->
>    _P (PAIR i x))
>   tcaseOP
>     where
>       tcaseOP = 
>         eat "_I" $ \_I -> 
>         eat "Cs" $ \_Cs -> 
>         eat "Ds" $ \_Ds -> 
>         eat "i" $ \i -> 
>         eat "x" $ \x -> 
>         eat "P" $ \_P -> 
>         eat "m" $ \m ->
>         emit $ wr (def iinductionDEF) _I (la "i'" $ \i' -> IFSIGMA (wr _Cs) (P (2,"Ds",error "A") :$ (B0 :< A i'))) i x _P
>                  (la "j" $ \j -> la "y" $ \y -> la "yh" $ \yh ->
>                   wr (def switchDEF) (wr _Cs) (V (Fs Fz) :$ (B0 :< Hd)) (la "c" $ \c ->
>                     ("i'", wr _I) ->> \i' ->
>                     ("xs", wr (def idescDEF) (wr _I) 
>                       (wr (def switchDEF) (wr _Cs) c (LK $ wr (def iDescDEF) (wr _I)) (P (2, "Ds", error "B") :$ (B0 :< A i')))
>                       (la "i''" $ \i'' -> IMU (wr _I) (la "i'''" $ \i''' -> IFSIGMA (wr _Cs) (P (2,"Ds",error "C") :$ (B0 :< A i'))) i'')) ->> \xs ->
>                     P (5, "P", error "D") :$ (B0 :< A (PAIR i' (CON (PAIR c xs)))))
>                    (wr m) j (V (Fs Fz) :$ (B0 :< Tl)))

> fstDEF :: DEF
> fstDEF = mkDEF
>   [("PRIM",0),("fst",0)]
>   (("S", SET) ->> \_S ->
>    ("T", ARR _S SET) ->> \_T ->
>    ("x", ("s", _S) -** \s -> _T s) ->> \x ->
>    _S)
>   (\_ -> Eat (|"S"|) $ Eat (|"T"|) $ Eat (|"x"|) $ Emit $ P (2,"x",undefined) :$ (B0 :< Hd))

> sndDEF :: DEF
> sndDEF = mkDEF
>   [("PRIM",0),("snd",0)]
>   (("S", SET) ->> \_S ->
>    ("T", ARR _S SET) ->> \_T ->
>    ("x", ("s", _S) -** \s -> _T s) ->> \x ->
>    _T (wr (def fstDEF) _S _T x))
>   (\_ -> Eat (|"S"|) $ Eat (|"T"|) $ Eat (|"x"|) $ Emit $ P (2,"x",undefined) :$ (B0 :< Tl))

> substDEF :: DEF
> substDEF = mkDEF
>   [("PRIM",0),("subst",0)]
>   (("X", SET) ->> \_X ->
>    ("x", _X) ->> \x ->
>    ("y", _X) ->> \y ->
>    ("eq", PRF (EQ _X x _X y)) ->> \_ ->
>    ("P", ARR _X SET) ->> \_P -> 
>    _P x --> _P y)
>   substOP
>     where
>       substOP = eat "X" $ \_X -> eat "x" $ \x -> eat "y" $ \y ->
>                  eat "eq" $ \eq -> eat "P" $ \_P -> eat "p" $ \p ->
>                   emit $ Coeh Coe (_P x) (_P y) 
>                            (Refl (ARR _X SET) _P :$ (B0 :< QA x y eq)) p :$ B0

> prims :: [ DEF ] 
> prims = [  idDEF , uncurryDEF , zeroElimDEF , falseElimDEF , inhElimDEF  
>         ,  branchesDEF , switchDEF , iDescDDEF , iDescDEF , idescDEF 
>         ,  iAllDEF , iallDEF , iinductionDEF , tindDEF , fstDEF , sndDEF , substDEF ]
