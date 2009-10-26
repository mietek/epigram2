\section{Tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Tactics where

Export |Tac| abstractly.

> import Control.Monad
> import Debug.Trace

> import BwdFwd

We ought to be able to get rid of Root import, and parameterize
everything by a Functor/Monad/Rooty m.

> import Root
> import Rooty
> import Tm
> import Rules

%endif

\subsection{The machinery}

> newtype Tac x = Tac { runTac :: Root -> TY -> Maybe x }

> instance Functor Tac where
>     fmap f g = Tac { \r t -> fmap f (runTac g r t) }

> instance Monad Tac where
>     return x = Tac { runTac = \_ _ -> Just x }
>     x >>= f = Tac { runTac = \r t -> 
>                                do 
>                                x <- runTac x r t
>                                runTac (f x) r t }

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
> discharge ref val = Rooty.freshRef ("dischargeTac" :<: val)
>                                    (\ref' -> undefined)

\subsection{Syntax-directed tacticals}

Intros

> lambda :: (VAL -> Tac VAL) -> Tac VAL
> lambda body = 
>     Tac { runTac = \root typ ->
>           case typ of 
>             C (Pi s t) ->
>                 fresh ("lambdaTac" :<: s)
>                       (\val root' -> 
>                            do
>                              term <- runTac (body val) root' (t $$ A val)
>                              return (L (H B0 "lambdaTac" (bquote term root'))))
>                       root
>             _ -> Nothing
>           }
       
> can :: Can (Tac VAL) -> Tac VAL
> can Set = 
>     Tac { runTac = \root typ ->
>           case typ of
>             SET -> do
>                    return SET
>             _ -> Nothing                  
>         }
> can (Pi tacS tacT) =
>     Tac { runTac = \root typ ->
>           case typ of
>             SET -> do
>                      s <- runTac tacS root SET
>                      t <- runTac tacT root (C (Pi s SET))
>                      return (C (Pi s t))
>             _ -> Nothing 
>         }

Elim

> newtype Use = Use { runUse :: (NEU :<: TY) -> Tac VAL }

> done :: Use
> done =
>   Use { runUse = \(v :<: t) ->
>     Tac { runTac = \root typ ->
>                    if equal (SET :>: (typ, t)) root then
>                       do
>                       check (typ :>: bquote (N v) root) root
>                       return (N v)
>                    else
>                        Nothing
>         }
>       }

> use :: REF -> Use -> Tac VAL
> use ref useR = 
>     Tac { runTac =
>             runTac $ runUse useR (P ref :<: pty ref)
>         }

> apply :: Tac VAL -> Use -> Use
> apply tacX use = 
>     Use { runUse = \(f :<: t) ->
>             Tac { runTac = \root typ ->
>                     case t of
>                       C (Pi s t) ->
>                         do
>                         xv <- runTac tacX root s
>                         runTac (runUse use (f :$ A xv :<: t $$ A xv))
>                                root
>                                typ
>                       _ -> Nothing
>                 }
>         }
