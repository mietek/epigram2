> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, FlexibleContexts #-}

> module Evidences.TypeCheckRules where

> import Control.Applicative
> import Control.Monad.Error

> import Evidences.Tm
> import Evidences.ErrorHandling

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

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
> canTy ((Prf, [_P]) :>: p)            = case (ev _P, p) of
>   (ONE, Zero) -> (| ONE |)
>   (INH _T, Wit) -> (| (_T *** ONE) |)
>   (AND _P _Q, Pair) -> (| (PRF _P *** PRF _Q *** ONE) |)
>   (Eq :- [_S, s, _T, t], c) -> case (ev _S, ev _T) of
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
> canTy ((Set, []) :>: EnumU)          = (| ONE |)
> canTy ((Set, []) :>: EnumT)          = (| (ENUMU *** ONE) |)
> canTy ((EnumU, []) :>: NilE)         = (| ONE |)
> canTy ((EnumU, []) :>: ConsE)        = (| (UID *** ENUMU *** ONE) |)
> canTy ((EnumT, [_,_]) :>: Ze)        = (| ONE |) 
> canTy ((EnumT, [_,e]) :>: Su)        = (| (ENUMT e *** ONE) |) 
> -- [/Feature = Enum]

> canTy _ = (|)


> projable :: VAL -> Maybe (TY, Tm {Body, s, Z} -> TY)
> projable (SIGMA s t)         = Just (s, (t $$.))
> projable (PRF _P) = case ev _P of
>   AND _P _Q  -> Just (PRF _P, \_ -> PRF _Q)
>   Eq :- [_S, s, _T, t] -> case (ev _S, ev _T) of
>     (_C :- es, _C' :- es') -> case eqUnfold ((_C, es) :>: s) ((_C', es') :>: t) of
>       Just (Pair, [_P, _Q]) -> Just (PRF _P, \_ -> PRF _Q)
>       _ -> (|)
>     _ -> (|)
>   _            -> (|)
> projable _                = Nothing



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
>    in  Eq :- [nix _S, s, nix _S', s'] ==>
>        Eq :- [nix _T :$ ss, nix f :$ ss, nix _T' :$ ss', nix f' :$ ss']])
> eqUnfold ((Sigma, [_S, _T]) :>: p) ((Sigma, [_S', _T']) :>: p') =
>   pure (Pair, [Eq :- [_S, s, _S', s'], Eq :- [_T $$. s, t, _T' $$. s', t']])
>   where s = p $$ Hd ; t = p $$ Tl ; s' = p' $$ Hd ; t' = p $$ Tl
> eqUnfold ((Prf, [_]) :>: _) ((Prf, [_]) :>: _) = pure (Zero, [])
> eqUnfold _ _ = pure (Con, [ZERO])

> eqSetUnfold :: VAL -> VAL -> Maybe (Can, [EXP])
> eqSetUnfold SET SET = pure (Zero, [])
> eqSetUnfold (PI _S _T) (PI _S' _T') = pure (Pair,
>   [  Eq :- [SET, _S, SET, _S']
>   ,  Eq :- [_S --> SET, _T, _S' --> SET, _T']])
> eqSetUnfold (SIGMA _S _T) (SIGMA _S' _T') = pure (Pair,
>   [  Eq :- [SET, _S, SET, _S']
>   ,  Eq :- [_S --> SET, _T, _S' --> SET, _T']])
> eqSetUnfold (PRF _P) (PRF _Q) =
>   pure (Pair, [_P ==> _Q, _Q ==> _P])
> eqSetUnfold _ _ = pure (Con, [ZERO])

