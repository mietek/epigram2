\section{Tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Tactics where

Export |Tac| abstractly.

> import Control.Monad
> import Control.Applicative
> import Debug.Trace

> import BwdFwd
> import Rooty
> import Root
> import Tm
> import Rules

%endif

\subsection{The machinery}

> newtype Tac x = Tac { runTac :: Root -> TY -> Maybe x }

> instance Functor Tac where
>     fmap f g = Tac { runTac = \r t -> fmap f (runTac g r t) }

> instance Applicative Tac where
>     pure x = Tac { runTac = \_ _ -> Just x }
>     f <*> x = Tac { runTac = \r t ->
>                              do 
>                              f' <- runTac f r t
>                              x' <- runTac x r t
>                              return $ f' x' }

> instance Monad Tac where
>     return = pure
>     x >>= f = Tac { runTac = \r t -> 
>                                do 
>                                x <- runTac x r t
>                                runTac (f x) r t }

> instance Rooty Tac where
>     freshRef x tacF = Tac { runTac = Rooty.freshRef x (runTac . tacF) }
>     forkRoot s child dad = Tac { runTac = \root typ -> 
>                                           do 
>                                           c <- runTac child (room root s) typ
>                                           runTac (dad c) (roos root) typ
>                                }

\subsection{The tactic combinators}

This is the only place where we are allowed to play inside |Tac { ... }|.

\subsubsection{Setting goals}

This is a bit of Reader digest: |ask| and |runReader|.

> goal :: Tac TY
> goal = Tac { runTac = \root typ -> Just typ }

> subgoal :: TY -> Tac x -> Tac x
> subgoal typ tacX = 
>     Tac { runTac = \root typ' -> 
>           do
>           guard $ equal (SET :>: (typ, typ')) root 
>           runTac tacX root typ
>         }

\subsubsection{}

> discharge :: Rooty m => REF -> VAL -> m VAL
> discharge freshRef val = (|(\t -> L (H B0 "discharge" t)) 
>                            (quoteRef' [freshRef] val) |)

\subsection{Syntax-directed tacticals}

Intros

> lambda :: (VAL -> Tac VAL) -> Tac VAL
> lambda body = do
>   C (Pi s t) <- goal
>   Rooty.freshRef ("" :<: s) $
>                  \x -> 
>                      discharge x =<<
>                      subgoal (t $$ A (pval x)) (body (pval x))

This one should use the modified version of canTy:
       
> can :: Can (Tac VAL) -> Tac VAL
> can Set = do
>           SET <- goal
>           return SET
> can (Pi tacS tacT) = do
>   SET <- goal
>   s <- subgoal SET tacS
>   t <- subgoal (C (Pi s SET)) tacT
>   return $ C (Pi s t)

Elim

> type Use = (NEU :<: TY) -> Tac VAL

> done :: Use
> done (v :<: t) =
>     do
>       vv <- subgoal t $
>             (do
>               return $ N v)
>       return vv

> use :: REF -> Use -> Tac VAL
> use ref useR = 
>     do
>       useR (P ref :<: pty ref)

> apply :: Tac VAL -> Use -> Use
> apply tacX use (f :<: C (Pi s t)) = 
>     do
>     x <- subgoal s tacX
>     use (f :$ A x :<: t $$ A x)

