\section{Tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Tactics (Tac,                      -- abstract Tactic
>                 goal, subgoal, discharge, -- low-level combinators
>                 lambda, can,              -- introduction rules
>                 done, use, apply          -- elimination rules
>                 ) where

> import Control.Monad
> import Control.Applicative

> import Data.Traversable

> import BwdFwd
> import Rooty
> import Root
> import Tm
> import Rules

%endif

The Tactic systems allow us to build well-typed terms from within
Haskell, with relative ease. To do that, we have equipped the |Tac|
data-type with adequate structure, and a set of combinators.

In a first section, we implement |Tac| and dress it up with its
structure. In a second section, we implement the combinators. 

\subsection{The machinery}

A Tactic is something that builds a term of a given type. In
this process, it might be required to create fresh names, hence the
availability of a |Root|. All in all, this goes like this:

> newtype Tac x = Tac { runTac :: Root -> TY -> Maybe x }

In other words, we have two @Reader@ monads stacked on an @Error@
monad. I don't know for you but I'm quite happy to reinvent the wheel
by not using the wacky monad transformers.

\subsubsection{Being monadic}

The corollary is that we have to implement the standard mumbo jumbo
for monads. First, we have a functor:

> instance Functor Tac where
>     fmap f g = Tac { runTac = \r t -> fmap f -- in Maybe functor
>                                            (runTac g r t) }

Then we have a monad:

> instance Monad Tac where
>     return x = Tac { runTac = \_ _ -> Just x }
>     x >>= f = Tac { runTac = \r t -> 
>                                do -- in Maybe monad
>                                x <- runTac x r t
>                                runTac (f x) r t }
>
> instance MonadPlus Tac where
>     mzero = Tac { runTac = \_ _ -> Nothing }
>     a `mplus` b = Tac { runTac = \r t -> runTac a r t `mplus` runTac b r t }

\subsubsection{Going rooty}

Because a tactic is some sort of |(->) Root |, it is also a
|Rooty|. Therefore, we abstractly get |freshRef| and |forkRoot|
operations on it. 

Let us work out the implementation:

> instance Rooty Tac where
>     root = Tac { runTac = \root _ -> Just root }
>     freshRef x tacF = Tac { runTac = Rooty.freshRef x (runTac . tacF) }
>     forkRoot s child dad = Tac { runTac = \root typ -> 
>                                           do 
>                                           c <- runTac child (room root s) typ
>                                           runTac (dad c) (roos root) typ
>                                }

Which requires |Tac| to be applicative. This is not a trouble now that
we have a monad:

> instance Applicative Tac where
>     pure = return
>     (<*>) = ap


\subsection{The tactic combinators}

The combinators are implemented in two layers. In this section, we are
concerned by the lower-level layer: we implement the only combinators
which are allowed to manipulate the inner structure of |Tac {...}|.

This is rougly decomposed in two parts: one to deal with the |TY ->|
arrow in |Tac|, the other to deal with the |Root ->| arrow. The
|Maybe| aspect of |Tac| is automatically dealt with the monadic
definition. Similarly, the |Root| aspect might seem poorly equipped:
bear in mind that |Tac| is also |Rooty|.

\subsubsection{Setting goals}

As we have mentionned |TY ->| is a Reader, so are its
combinators. 

Hence, we can |ask| what is the current type goal with, well,
|goal|. 

This is a bit of Reader digest: |ask| and |runReader|.

> goal :: Tac TY
> goal = Tac { runTac = \root typ -> Just typ }

|subgoal| is the |local| of Reader that runs |tacX| in a local |typ|
environment. Conor is concerned about the fact that, apart from
Inference rules, nobody should be using this guy.

> subgoal :: TY -> Tac x -> Tac x
> subgoal typ tacX = 
>     Tac { runTac = \root typ' -> 
>              runTac tacX root typ }

\subsubsection{Making lambdas}

Given a value, we might want to discharge an hypothesis used deep down
in it. That is, provided a free variable |ref|, we have to track it
inside |val| and, when found, bind it to the De Bruijn index 0. This
is quoting. Then, well, we put that under a lambda and we are
discharged.

> discharge :: Rooty m => REF -> VAL -> m VAL
> discharge ref val = (| (L . (H B0 "discharge")) 
>                        (bquote (B0 :< ref) val) |)

As mentioned above, we should not forget that |Tac| is in |Rooty|: we
have |freshRef| and |forkRoot| for free.

\subsection{Syntax-directed tacticals}

Based on the low-level combinators defined in the previous section, we
can build more powerful combinators. In particular, we are interested
in recovering some kind of expressivity: our high-level tactics follow
the syntax of the language, without the cruft (De Bruijn indices,
trivial type checks, \ldots).

This is decomposed in two sections: first, introduction rules, then
elimination rules.

\subsubsection{Introduction rules}

Here is a tip to decypher the types below. The type |Tac VAL| can be
read as "something that will build a well-typed value". I mean, that's
the whole purpose of these tactics, anyway.

The first combinator is our beloved |lambda|. It turns an Haskell
function using a value to build a well-typed term into a well-typed
term. 

> lambda :: (REF -> Tac VAL) -> Tac VAL
> lambda body = do
>   C (Pi s t) <- goal
>   Rooty.freshRef ("" :<: s) $
>                  \x -> do
>                    body <- subgoal (t $$ A (pval x)) (body x)
>                    discharge x body

Similarly, we can also implement the typed lambda, for which variable
types are known. If |lambda| were a bit more polymorphic, we could use
it here I think.

> tyLambda :: (String :<: TY) -> (REF -> Tac (VAL :<: TY))
>                             -> Tac (VAL :<: TY)
> tyLambda (name :<: s) body = do
>     C (Pi s t) <- goal
>     Rooty.freshRef ("" :<: s) $
>                    \x -> do
>                      (body :<: ts) <- subgoal (t $$ A (pval x)) (body x)
>                      v <- discharge x body
>                      t <- discharge x ts
>                      return $ v :<: C (Pi s t)

The second builder is significantly simpler, as we don't have to care
about binding. Taking a canonical term containing well-typed values,
|can| builds a well-typed (canonical) value.

To do that, we first ask our goal to live in the canonical
world. That's an obvious requirement. Then, we use the canonical
type-checker (with the identity as an evaluation function, because we
don't have to evaluate terms) to check that |cTac| lives in |t|. The
result is a |Tac (Can (TY :>: Tac VAL))|. Meaning that in the |Tac|
monad, |v| has type |Can (TY :>: Tac VAL)|. But do we care about 
|TY :>: .|? Surely not, so we drop this information and just return the
canonical value.

> can :: Can (Tac VAL) -> Tac VAL
> can cTac = do
>     C t <- goal
>     v <- canTy id (t :>: cTac)
>     v <- traverse (\(t :>: v) -> v) v
>     return $ C v



> infr :: TY -> Tac VAL -> Tac (VAL :<: TY)
> infr typ tacX = do
>   typ <- goal
>   x <- tacX
>   return (x :<: typ)

\subsubsection{Elimination rules}

Elimination rules are manipulating the following type:

> type Use = (NEU :<: TY) -> Tac VAL

Which says something like "provided a value of inferred type, I have a
well-typed value". This is used to handle the |In| terms of the
language, by some sort of continuation-passing style
construction. More on that style with |apply|.

Confirming the insight behind |Use|, here is the definition of
|done|. This operators closes the continuation by stopping the guess
work and comparing the inferred type with the goal.

> done :: Use
> done (v :<: typ) =
>     do
>       typ' <- goal
>       p <- equalR (SET :>: (typ, typ'))
>       guard p
>       return $ N v

One the other hand, |apply| builds up the continuation. It builds an
|Use| which \emph{emph} must be a function, this function being
applied to the value inside |tacX|. Once the result has been computed,
the |use| continuation is called.

> apply :: Tac VAL -> Use -> Use
> apply tacX use (f :<: C (Pi s t)) = 
>     do
>     x <- subgoal s tacX
>     use (f :$ A x :<: t $$ A x)

Finally, the continuation is created by |use| that, basically, allows
you to apply the arguments built in |useR| to the function |ref|erenced.

> use :: REF -> Use -> Tac VAL
> use ref useR = 
>     do
>       useR (P ref :<: pty ref)

%if false

> f = undefined
> x1 = undefined
> x2 = undefined

%endif

Therefore, we are able to write a standard function application as
simply as:

> example = use f . apply x1 . apply x2 $ done