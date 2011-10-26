\section{Type-checker}
\label{sec:Evidences.TypeChecker}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
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
> import Evidences.Primitives
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
>   return (ev (g :/ exp t))

> chk :: (Applicative m, MonadError StackError m, {: p :: Part :}) => 
>            Int -> TY :>: (Env {Z} {n}, Tm {p, s, n}) -> m ()
> chk l (_T :>: (g, Con :- [x])) | B (SIMPLDTY na _I uDs) :$ (B0 :< A i) <- ev _T =
>   chk l (D idescDEF :$ (B0 
>              :< A _I 
>              :< A (IFSIGMA (D constrDEF :$ (B0 :< A _I :< A uDs))
>                            (D conDDEF :$ (B0 :< A _I :< A uDs :< A i)))
>              :< A (B (SIMPLDTY na _I uDs) :$ B0)) :>: (g, x))  
> chk l (_T :>: (g, c :- es)) = case ev _T of
>   _C :- as -> do
>     _Ts <- canTyM ((_C, as) :>: c)
>     chks l (_Ts :>: (g, es))
>   _ -> throwError' $ err "canonical inhabitant of non-canonical type"
> chk l (_T :>: (g, L g' x b)) = case lambdable (ev _T) of
>   Just (_, _S, _T) -> chk (l + 1) (_T x' :>: (ENix, evalEager {Exp} (g <+< g' <:< x') b)) where
>     x' = P (l, x, _S) :$ B0
>   _ -> throwError' $ err ("lambda inhabiting non-canonical type: " ++ 
>                       (show $ ev _T))
> chk l (_T :>: (g, LK b)) = case lambdable (ev _T) of 
>   Just (_, _S, _T) -> chk l (_T undefined :>: (ENix, evalEager {Exp} g b)) 
>   _ -> throwError' $ err ("klambda inhabiting non-canonical type")

< chk l (_T :>: (g, t@(V _ :$ _))) = chk l (_T :>: (ENil, eval {Val} g t))
< chk l (_T :>: (g@(gl,_), t@(P (pl,_,_) :$ _))) | Just _ <- lookup pl gl = 
<   chk l (_T :>: (ENil, eval {Val} g t))

< chk l (_T :>: (g, g' :/ t)) = chk l (_T :>: (g <+< g', t))
< chk l (_T :>: (g, t :$ B0)) = chk l (_T :>: (g , t))

< chk l (_T :>: (g, t@(h :$ _))) | isRedHead h
<     = chk l (_T :>: (ENil, eval {Val} g t))
<   where
<     isRedHead :: Tm {p, s, n} -> Bool
<     isRedHead (h :$ B0)  = isRedHead h
<     isRedHead (_ :/ h)   = isRedHead h
<     isRedHead (V _)      = True
<     isRedHead (LK _)     = True
<     isRedHead (L _ _ _)  = True
<     isRedHead _          = False

> chk l (_T :>: t@(g,tm)) = do
>   _T' <- inf l (g, tm)
>   if equal l (SET :>: (_T, _T'))
>       then return ()
>       else throwError' $ [  StrMsg "Inferred type: "
>                          ,  ErrorTm (Just SET :>: _T')
>                          ,  StrMsg "is not equal to expected type:" 
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
>                        m (EXP :<: TY, [Elim (Tm {Body, Exp, n})])
> headTySpine l (g, g' :/ h)       = do
>   (ety, as) <- headTySpine l (g <+< g', h)
>   return (ety, map (fmap (g' :/)) as)
> headTySpine l (g, D d)      = 
>   pure (D d :$ B0 :<: defTy d, [])
> headTySpine l (g@(gl,_), p@(P (_,_,ty))) = 
>   (| (eval {Exp} g p :<: ((gl, INix) :/ ty), []) |)
> headTySpine l (g, Refl _S s)     = do
>   _S <- chev l (SET :>: (g, _S))
>   let _S' = exp _S
>   s <- chev l (exp _S :>: (g, s))
>   let s' = exp s
>   return ((Refl _S' (exp s') :$ B0) :<: PRF (Eq :- [_S', s', _S', s']), [])
> headTySpine l (g, Coeh c _S _T _Q s) = do
>   _S <- chev l (SET :>: (g, _S))
>   _T <- chev l (SET :>: (g, _T))
>   _Q <- chev l (PRF (Eq :- [SET, exp _S, SET, exp _T]) :>: (g, _Q))
>   s <- chev l (exp _S :>: (g, s))
>   let (s', q') = coeh _S _T _Q s
>   case c of
>     Coe -> return (exp s' :<: exp _T, [])
>     Coh -> return (exp q' :<: PRF (Eq :- [exp _S, exp s, exp _T, exp s']), [])
> headTySpine l (g, B d@(SIMPLDTY name _I uDs)) = do
>   return (B d :$ B0 :<: _I --> SET, [])
> headTySpine l (g, h :$ as)       = do 
>   (ety, as') <- headTySpine l (g,h) 
>   return (ety, (as' ++ trail as))
> headTySpine _ (g, h)             = poof {: p :: Part :} g h where
>   poof ::  forall s m n . (MonadError StackError m) => 
>            pi (p :: Part). Env {Z} {n} -> Tm {p, s, n} ->
>            m (EXP :<: TY, [Elim (Tm {Body, Exp, n})])
>   poof {Head} g h = throwError' $
>     err "headTySpine with bad head " ++ errTm (g :/ (exp h :$ B0))
>   poof {Body} g h = throwError' $
>     err "headTySpine with bad head " ++ errTm (g :/ exp h)



> spInf :: (Applicative m, MonadError StackError m) => 
>              Int -> (EXP :<: TY) ->
>                  (Env {Z} {n}, [Elim (Tm {Body, s, n})]) -> m TY
> spInf l (_ :<: _T) (g, [])     = pure _T
> spInf l (e :<: _T) (g, a:as) = case (ev _T, a) of
>     (_T, A a) -> case lambdable _T of 
>       Just (_, _S, _T) -> do
>         a <- chev l (_S :>: (g, a))
>         spInf l (e $$. a :<: _T a) (g, as)
>       Nothing -> throwError' $ err "spInf:" ++ errTyTm (SET :>: wk _T) ++ err "not lambdable"
>     (_T, Hd) -> case projable _T of
>       Just (_S, _T)  -> spInf l (e $$ Hd :<: _S) (g, as)
>       Nothing -> throwError' $ err "spInf: not projable"
>     (_T, Tl) -> case projable _T of
>       Just (_S, _T)  -> spInf l (e $$ Tl :<: _T (e $$ Hd)) (g, as)
>       Nothing -> throwError' $ err "spInf: not projable"
>     (_T, Out) -> case outable _T of
>       Just _S -> spInf l (e $$ Out :<: _S) (g, as)
>       Nothing -> throwError' $ err "spInf: not outable"
>     -- [Feature = Prop]
>     (PRF _P, QA s u q)  -> case ev _P of
>       Eq :- [_X, f, _Y, h] -> case (ev _X, ev _Y) of
>         (PI _S _T, PI _U _V) -> do
>           s <- chev l (_S :>: (g, s))
>           u <- chev l (_U :>: (g, u))
>           q <- chev l (PRF (Eq :- [_S, exp s, _U, exp u]) :>: (g, q))
>           spInf l (e $$ QA s u q
>                   :<: PRF (Eq :- [_T $$. s, f $$. s, _V $$. u, h $$. u]))
>             (g, as)
>         _ -> throwError' $ err "spInf: applied equation not between functions"
>       _ -> throwError' $ err "spInf: equation application on non-equation"
>     (PRF _P, Sym)  -> case ev _P of
>       Eq :- [_X, x, _Y, y] -> spInf l (e $$ Sym :<: PRF (Eq :- [_Y, y, _X, x])) (g, as)
>       _ -> throwError' $ err "spInf: symmetry on non-equation"
>     -- [/Feature = Prop]
>     -- [Feature = Label]
>     (LABEL _T _, Call lab) -> do
>       a <- chev l (_T :>: (g, lab)) 
>       spInf l (e $$ Call a :<: _T) (g, as) 
>     -- [/Feature = Label]
>     (_T,_)         -> throwError' $ err ("spInf: bad " ++ show e)


> inf :: (Applicative m, MonadError StackError m, {: p :: Part :}) => 
>            Int -> (Env {Z} {n}, Tm {p, s, n}) -> m TY
> inf l (g, h :$ ss) = do
>   (tty, es) <- headTySpine l (g, h)
>   _T <- spInf l tty (g, es ++ trail ss)
>   return _T
> inf l (g, g' :/ t) = inf l (g <+< g', t)
> inf l ((gl,_), P (_,_,t)) = (| ((gl,INix) :/ t) |) 
> inf l (g, t) = do
>   (tty, es) <- headTySpine l (g, t)
>   _T <- spInf l tty (g, es)
>   return _T


> polyIdTy, polyIdTm, compTy, compTm, badCompTm :: EXP
> polyIdTy = ("_X", SET) ->> \ _X -> ARR _X _X
> polyIdTm = LK $ la "x" $ \ x -> x

> compTy = (SET --> SET) --> (SET --> SET) --> SET --> SET
> compTm = la "g" $ \ g -> la "f" $ \ f -> la "x" $ \ x -> g (f x)
> badCompTm = la "g" $ \ g -> la "f" $ \ f -> la "x" $ \ x -> f
