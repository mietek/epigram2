\section{TypeCheckRules}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, FlexibleContexts #-}

> module Evidences.TypeCheckRules where

> import Control.Applicative
> import Control.Monad.Error

> import Evidences.Tm
> import Evidences.Primitives
> import Evidences.ErrorHandling

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

%endif

> canTy :: (Can, [EXP]) :>: Can -> Maybe VAL
> canTy ((Set, []) :>: Set)            = (| ONE |)
> canTy ((Set, []) :>: Pi)             = 
>   pure $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: Sigma)          =
>   pure $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: Zero)           = (| ONE |)
> canTy ((Set, []) :>: One)            = (| ONE |)

> canTy ((Sigma, [_S, _T]) :>: Pair)   = 
>   pure $ ("s", _S) -** \ s -> wr _T s *** ONE
> canTy ((One, []) :>: Zero)           = (| ONE |)

> -- [Feature = Prop]
> canTy ((Set, []) :>: Prop)           = (| ONE |)
> canTy ((Set, []) :>: Prf)            = (| (PROP *** ONE) |)
> canTy ((Prop, []) :>: Pi)            = 
>   (| (("S", SET) -** \ _S -> ARR _S PROP *** ONE) |)
> canTy ((Prop, []) :>: Zero)          = (| ONE |)
> canTy ((Prop, []) :>: One)           = (| ONE |)
> canTy ((Prop, []) :>: Inh)           = (| (SET *** ONE) |)
> canTy ((Prop, []) :>: And)           = (| (PROP *** PROP *** ONE) |)
> canTy ((Prop, []) :>: Eq)            = pure $
>   (("S", SET) -** \ _S -> _S ***
>    ("T", SET) -** \ _T -> _T *** ONE)
> canTy ((Prf, [_P]) :>: p)            = case (ev _P, p) of
>   (ONE, Zero) -> (| ONE |)
>   (INH _T, Wit) -> (| (_T *** ONE) |)
>   (AND _P _Q, Pair) -> (| (PRF _P *** PRF _Q *** ONE) |)
>   (EQ _S s _T t, c) -> case (ev _S, ev _T) of
>     (_C :- es, _C' :- es') -> case eqUnfold ((_C, es) :>: s) ((_C', es') :>: t) of
>       Just (c', _Ps) | c == c' -> (| (prfs _Ps) |)
>       _ -> (|)
>     _ -> (|)
>   _ -> (|)
>   where
>     prfs :: [EXP] -> Tm {Body, s, Z}
>     prfs [] = ONE
>     prfs (_P : _Ps) = PRF _P *** prfs _Ps
> -- [/Feature = Prop]
> -- [Feature = UId]
> canTy ((Set, []) :>: UId)            = (| ONE |)
> canTy ((UId, []) :>: Tag _)          = (| ONE |)
> -- [/Feature = UId]
> -- [Feature = Enum]
> canTy ((Set, []) :>: EnumT)          = (| (def enumUDEF *** ONE) |)
> canTy ((EnumT, [_E]) :>: n)          = case (evv _E, n) of
>   (CONSE _ _, Ze) -> (| ONE |) 
>   (CONSE _ _E', Su) -> (| (ENUMT _E' *** ONE) |) 
> -- [/Feature = Enum]
> -- [Feature = IDesc]
> canTy ((Set, []) :>: IMu)    =
>   pure $ ("I", SET) -** \ _I -> 
>          ("D", ARR _I (wr (def iDescDEF) _I)) -** \ _D -> 
>          ("i", _I) -** \ _ -> ONE
> canTy ((IMu, [_I, _D, i]) :>: Con) = 
>   pure $ ("x", wr (def idescDEF) _I (wr _D i) 
>                      (la "i'" $ \i' -> IMU (nix _I) (nix _D) i')) -**
>          \ _ -> ONE
> -- [/Feature = IDesc]
> -- [Feature = Label]
> canTy ((Set, []) :>: Label)          = 
>   pure $ ("T", SET) -** \ _T -> _T *** ONE
> canTy ((Label, [_T, _]) :>: Ret) = (| (_T *** ONE) |)
> -- [/Feature = Label]
> -- [Feature = List]
> canTy ((Set, []) :>: List) = pure $ ("A", SET) -** \ _A -> ONE
> canTy ((List, [_A]) :>: Nil) = pure ONE
> canTy ((List, [_A]) :>: Cons) = pure $ (_A *** LIST _A *** ONE)
> -- [/Feature = List]
> -- [Feature = Scheme]
> canTy ((Set, []) :>: Scheme) = (| ONE |)
> canTy ((Scheme, []) :>: SchTy) = pure $ ("T", SET) -** \ _T -> ONE
> canTy ((Scheme, []) :>: SchPi) = pure $ ("S", SCHEME) -** \ _S -> ("T", wr (def schElDEF) _S --> SCHEME) -** \ _T -> ONE
> canTy ((Scheme, []) :>: SchImPi) = pure $ ("S", SET) -** \ _S -> ("T", _S --> SCHEME) -** \ _T -> ONE
> -- [/Feature = Scheme]
> -- [Feature = Dubbing]
> canTy ((Set, []) :>: Dub) = pure $ ("u", UID) -** \u -> ("S", SET) -** \_S -> ("s", _S) -** \_ -> ONE
> canTy ((Dub, [u, _S, s]) :>: Zero) = pure ONE
> -- [/Feature = Dubbing]

> canTy _ = (|)


> projable :: VAL -> Maybe (TY, Tm {Body, s, Z} -> TY)
> projable (SIGMA s t)         = Just (s, (t $$.))
> projable (PRF _P) = case ev _P of
>   AND _P _Q  -> Just (PRF _P, \_ -> PRF _Q)
>   EQ _S s _T t -> case (ev _S, ev _T) of
>     (_C :- es, _C' :- es') -> case eqUnfold ((_C, es) :>: s) ((_C', es') :>: t) of
>       Just (Pair, [_P, _Q]) -> Just (PRF _P, \_ -> PRF _Q)
>       _ -> (|)
>     _ -> (|)
>   _            -> (|)
> projable _                = Nothing



> outable :: VAL -> Maybe TY
> outable (PRF _P) = case ev _P of
>   EQ _S s _T t -> case (ev _S, ev _T) of
>     (_C :- es, _C' :- es') -> case eqUnfold ((_C, es) :>: s) ((_C', es') :>: t) of
>       Just (Con, [_Q]) -> Just (PRF _Q)
>       _ -> (|)
>     _ -> (|)
>   _ -> (|)
> outable (IMU _I _D i) = pure $ (D idescDEF) :$ (B0 :< A _I :< A (apply {Exp} _D (A i)) 
>                                                    :< A (L ENil "i'" $ IMU (nix _I) (nix _D) (toBody (V Fz))))
> outable _ = Nothing


> canTyM :: (Applicative m, MonadError StackError m) =>
>               (Can, [EXP]) :>: Can -> m VAL
> canTyM  x@((cty, es) :>: ct) = case canTy x of
>     Just v   -> return v
>     Nothing  -> throwError' $ err "canTy: canonical type"
>                               ++ errTyTm (SET :>: cty :- es)
>                               ++ err "does not admit"
>                               ++ errTm (ct :- [])

> eqUnfold :: ((Can, [EXP]) :>: EXP) -> ((Can, [EXP]) :>: EXP) -> Maybe (Can, [EXP])
> eqUnfold ((Set, []) :>: _A) ((Set, []) :>: _B) = eqSetUnfold (ev _A) (ev _B)
> eqUnfold ((Pi, [_S, _T]) :>: f) ((Pi, [_S', _T']) :>: f') = pure (Ext,
>   [("s", _S) ->> \ s -> ("s'", nix _S') ->> \ s' ->
>    let ss = B0 :< A s ; ss' = B0 :< A s'
>    in  EQ (nix _S) s (nix _S') s' ==>
>        EQ (nix _T :$ ss) (nix f :$ ss) (nix _T' :$ ss') (nix f' :$ ss')])
> eqUnfold ((Sigma, [_S, _T]) :>: p) ((Sigma, [_S', _T']) :>: p') =
>   pure (Pair, [EQ _S s _S' s', EQ (_T $$. s) t (_T' $$. s') t'])
>   where s = p $$ Hd ; t = p $$ Tl ; s' = p' $$ Hd ; t' = p' $$ Tl
> eqUnfold ((One, []) :>: _) ((One, []) :>: _) = pure (Zero, [])
> eqUnfold ((Prf, [_]) :>: _) ((Prf, [_]) :>: _) = pure (Zero, [])
> eqUnfold ((Prop, []) :>: _P) ((Prop, []) :>: _Q) = 
>   pure (Pair, [_P ==> _Q, _Q ==> _P])
> -- [Feature = IDesc]
> eqUnfold ((IMu, [_I, _D, i]) :>: x) ((IMu, [_I', _D', i']) :>: x') = 
>   pure (Con, 
>     [  EQ  (def idescDEF $$$. (B0 :< _I :< (_D $$. i) :< 
>              (L ENil "s" $ IMU (nix _I) (nix _D) (V Fz :$ B0)))) (x $$ Out)
>            (def idescDEF $$$. (B0 :< _I' :< (_D' $$. i') :< 
>              (L ENil "s" $ IMU (nix _I') (nix _D') (V Fz :$ B0)))) (x' $$ Out)
>     ])
> -- [/Feature = IDesc]
> -- [Feature = Enum]
> eqUnfold ((EnumT, [_E]) :>: e) ((EnumT, [_E']) :>: e') = case (ev _E, ev e, ev _E', ev e') of
>   (CONSE _ _, ZE, CONSE _ _, ZE) -> (|(Zero, [])|)
>   (CONSE _ _E, SU x, CONSE _ _E', SU y) -> (|(Con, [EQ (ENUMT _E) x (ENUMT _E') y])|)
>   (CONSE _ _, ZE, CONSE _ _, SU _) -> (| (Con, [ZERO]) |)
>   (CONSE _ _, SU _, CONSE _ _, ZE) -> (| (Con, [ZERO]) |)
>   (CONSE _ _, _, CONSE _ _, _) -> (|)
>   _ -> (| (Zero, []) |)
> -- [/Feature = Enum]
> -- [Feature = UId]
> eqUnfold ((UId, []) :>: t) ((UId, []) :>: t') = error "eqUnfold: UId"
> -- [/Feature = UId]
> -- [Feature = Scheme]
> eqSetUnfold ((Scheme, []) :>: s) ((Scheme, []) :>: s)  = error "eqUnfold: Scheme"
> -- [/Feature = Scheme]
> -- [Feature = Dubbing]
> eqUnfold ((Dub, _) :>: _) ((Dub, _) :>: _) = pure (Zero, [])
> -- [/Feature = Dubbing]
> eqUnfold _ _ = pure (Con, [ZERO])

> eqSetUnfold :: VAL -> VAL -> Maybe (Can, [EXP])
> eqSetUnfold (c :- []) (c' :- []) | c == c' = pure (Zero, [])
> eqSetUnfold (PI _S _T) (PI _S' _T') = pure (Pair,
>   [  EQ SET _S SET _S'
>   ,  EQ (_S --> SET) _T (_S' --> SET) _T'])
> eqSetUnfold (SIGMA _S _T) (SIGMA _S' _T') = pure (Pair,
>   [  EQ SET _S SET _S'
>   ,  EQ (_S --> SET) _T (_S' --> SET) _T'])
> eqSetUnfold (PRF _P) (PRF _Q) =
>   pure (Pair, [_P ==> _Q, _Q ==> _P])
> -- [Feature = IDesc]
> eqSetUnfold (IMU _I _D i) (IMU _I' _D' i') = pure (Pair,
>   [  EQ SET _I SET _I'
>   ,  AND  (EQ (ARR _I (def iDescDEF $$. _I $$. ZERO)) _D 
>               (ARR _I' (def iDescDEF $$. _I' $$. ZERO)) _D')
>           (EQ _I i _I' i') ])
> -- [/Feature = IDesc]
> -- [Feature = Enum]
> eqSetUnfold (ENUMT as) (ENUMT bs) = error "eqSetUnfold: ENUMT"
> -- [/Feature = Enum]
> -- [Feature = Dubbing]
> eqSetUnfold (DUB u _S s) (DUB u' _S' s') = error "eqSetUnfold: DUB"
> -- [/Feature = Dubbing]

> eqSetUnfold (_ :- _) (_ :- _) = pure (Con, [ZERO])
> eqSetUnfold _ _ = Nothing
