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
> import Evidences.ErrorHandling

%endif


> typeCheck :: (Applicative m, MonadError StackError m) =>
>                  (TY :>: EXP) -> m ()
> typeCheck (ty :>: t) = chk 0 (ty :>: (ENil, t))

>

It's just possible that variable-management should be baked into a monad,
here.

> chev :: (Applicative m, MonadError StackError m) => 
>             Int -> TY :>: (Env {Z} {n}, Tm {Body, s, n}) -> m VAL
> chev l prob@(_ :>: (g, t)) = do
>   chk l prob
>   return (ev (g :/ t))

> chk :: (Applicative m, MonadError StackError m) => 
>            Int -> TY :>: (Env {Z} {n}, Tm {Body, s, n}) -> m ()
> chk l (_T :>: (g, c :- es)) = case ev _T of
>   _C :- as -> do
>     _Ts <- canTyM ((_C, as) :>: c)
>     chks l (_Ts :>: (g, es))
>   _ -> throwError' $ err "canonical inhabitant of non-canonical type"
> chk l (_T :>: (g, L g' x b)) = case lambdable (ev _T) of
>   Just (_, _S, _T) -> chk (l + 1) (_T x' :>: (g <+< g' <:< x', b)) where
>     x' = P (l, x, _S) :$ B0
>   _ -> throwError' $ err "lambda inhabiting non-canonical type"
> chk l (_T :>: (g, LK b)) = case lambdable (ev _T) of
>   Just (_, _S, _T) -> chk (l + 1) (_T x' :>: (g, b)) where
>     x' =  P (l, "s", _S) :$ B0

> chk l (_T :>: (g, t@(V _ :$ _))) = chk l (_T :>: (ENil, eval {Val} g t))

> chk l (_T :>: (g, g' :/ t)) = chk l (_T :>: (g <+< g', toBody t))

> chk l (_T :>: t) = do
>   _T' <- inf l t
>   if equal l (SET :>: (_T, _T'))
>       then return ()
>       else throwError' $ [  StrMsg "Inferred type: "
>                          ,  ErrorTm (Just SET :>: _T')
>                          ,  StrMsg " is not equal to expected type: " 
>                          ,  ErrorTm (Just SET :>: _T)
>                          ]

> chks :: (Applicative m, MonadError StackError m) => 
>             Int -> VAL :>: (Env {Z} {n}, [Tm {Body, s, n}]) -> m ()
> chks l (ONE           :>:  (g, []))     = (|()|)
> chks l (SIGMA _S _T   :>:  (g, s : t))  = do
>   s' <- chev l (_S :>: (g, s))
>   chks l (ev (_T $$. s') :>: (g, t))
> chks _ _ = throwError' $ err "spine-checking failure"




> headTySpine :: (Applicative m, MonadError StackError m, {: p :: Part :} ) => 
>                    Int -> (Env {Z} {n}, Tm {p, s, n}) ->
>                        m (EXP :<: TY, [EXP])
> headTySpine l (g, g' :/ h)       = headTySpine l (g <+< g', h)
> headTySpine l (g, D d es _)      = pure (D d S0 (defOp d) :<: defTy d, rewindStk es [])
> headTySpine l (g, P (i, s, ty))  = pure (P (i, s, ty) :$ B0 :<: ty, [])
> headTySpine _ (g, h)             = throwError' $
>     err "headTySpine with bad head" ++ errTm (exp (ev (g :/ h :$ B0)))



> spInf :: (Applicative m, MonadError StackError m) => 
>              Int -> (EXP :<: TY) ->
>                  (Env {Z} {n}, [Elim (Tm {Body, s, n})]) -> m TY
> spInf l (_ :<: _T) (g, [])     = pure _T
> spInf l (e :<: _T) (g, a:as) = case (ev _T, a) of
>     (_T, A a) -> case lambdable _T of 
>       Just (_, _S, _T) -> do
>         a <- chev l (_S :>: (g, a))
>         spInf l (e $$. a :<: _T a) (g, as)
>       Nothing -> throwError' $ err "spInf: not lambdable"
>     (_T, Hd) -> case projable _T of
>       Just (_S, _T)  -> spInf l (e $$ Hd :<: _S) (g, as)
>     (_T, Tl) -> case projable _T of
>       Just (_S, _T)  -> spInf l (e $$ Tl :<: _T (e $$ Hd)) (g, as)
>     _         -> throwError' $ err "spInf: bad"


> inf :: (Applicative m, MonadError StackError m) => 
>            Int -> (Env {Z} {n}, Tm {Body, s, n}) -> m TY
> inf l (g, h :$ ss) = do
>   (tty, es) <- headTySpine l (g, h)
>   _T <- spInf l tty (g, map (A . wk) es ++ trail ss)
>   return _T
> inf l (g, d@(D _ _ _)) = do
>   (tty, es) <- headTySpine l (g, d)
>   _T <- spInf l tty (g, map (A . wk) es)
>   return _T
> inf _ _ = throwError' $ err "type inference failure"


> polyIdTy, polyIdTm, compTy, compTm, badCompTm :: EXP
> polyIdTy = ("_X", SET) ->> \ _X -> ARR _X _X
> polyIdTm = LK $ la "x" $ \ x -> x

> compTy = (SET --> SET) --> (SET --> SET) --> SET --> SET
> compTm = la "g" $ \ g -> la "f" $ \ f -> la "x" $ \ x -> g (f x)
> badCompTm = la "g" $ \ g -> la "f" $ \ f -> la "x" $ \ x -> f
