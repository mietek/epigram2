\section{Type-checker}
\label{sec:Evidences.TypeChecker}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.TypeChecker where

> import Prelude hiding (exp)

> import Control.Applicative
> import Control.Monad.Error

> import Data.Traversable

> import ShePrelude

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.NatFinVec

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.TypeCheckRules

%endif


> typeCheck :: (TY :>: EXP) -> Maybe ()
> typeCheck (ty :>: t) = chk 0 (ty :>: (ENil, t))


It's just possible that variable-management should be baked into a monad,
here.

> chev :: Int -> TY :>: (Env {Z, n}, Tm {Body, s, n}) -> Maybe VAL
> chev l prob@(_ :>: (g, t)) = do
>   chk l prob
>   return (ev (g :/ t))

> chk :: Int -> TY :>: (Env {Z, n}, Tm {Body, s, n}) -> Maybe ()
> chk l (_T :>: (g, c :- es)) = case ev _T of
>   _C :- as -> do
>     _Ts <- canTy ((_C, as) :>: c)
>     chks l (_Ts :>: (g, es))
>   _ -> (|)
> chk l (_T :>: (g, L g' x b)) = case ev _T of
>   PI _S _T -> chk (l + 1) (_T $$. x' :>: (g <+< g' <:< x', b)) where
>     x' = P (l, x, _S) :$ B0
>   _ -> (|)
> chk l (_T :>: (g, LK b)) = case ev _T of
>   PI _S _T -> chk (l + 1) (_T $$. x' :>: (g, b)) where
>     x' = P (l, "s", _S) :$ B0

> chk l (_T :>: (g, t@(V _ :$ _))) = chk l (_T :>: (ENil, eval {Val} g t))

> chk l (_T :>: (g, h :$ ss)) = do
>   (tty, es) <- headTySpine l (g, h)
>   _T' <- spInf l tty (g, map (A . wk) es ++ trail ss)
>   guard $ equal (SET :>: (_T, _T'))
>   return ()

> chk l (_T :>: (g, g' :/ t)) = chk l (_T :>: (g <+< g', toBody t))


> chks :: Int -> VAL :>: (Env {Z, n}, [Tm {Body, s, n}]) -> Maybe ()
> chks l (ONE           :>:  (g, []))     = (|()|)
> chks l (SIGMA _S _T   :>:  (g, s : t))  = do
>   s' <- chev l (_S :>: (g, s))
>   chks l (ev (_T $$. s') :>: (g, t))
> chks _ _ = (|)




> headTySpine :: Int -> (Env {Z, n}, Tm {Head, s, n}) -> Maybe (EXP :<: TY, [EXP])
> headTySpine l (g, D (x, ty, o) es _)  = pure (D (x, ty, o) S0 o :<: ty, rewindStk es [])
> headTySpine l (g, P (i, s, ty))       = pure (P (i, s, ty) :$ B0 :<: ty, [])
> headTySpine _ _                       = (|)



> spInf :: Int -> (EXP :<: TY) -> 
>          (Env {Z, n}, [Elim (Tm {Body, s, n})]) -> Maybe TY
> spInf l (_ :<: _T) (g, [])     = pure _T
> spInf l (e :<: _T) (g, a:as) = case (ev _T, a) of
>     (PI _S _T, A a) -> do
>         a <- chev l (_S :>: (g, a))
>         spInf l (e $$. a :<: _T $$. a) (g, as)
>     (SIGMA _S _T, Hd) -> spInf l (e $$ Hd :<: _S) (g, as)
>     (SIGMA _S _T, Tl) -> spInf l (e $$ Tl :<: _T $$. (e $$ Hd)) (g, as)





