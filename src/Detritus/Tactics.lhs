\section{Tactics}
\label{sec:tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables,
>     MultiParamTypeClasses #-}

> module Evidences.Tactics (Tac,                         -- abstract Tactic
>                           runTac,                      -- run tactics
>                           goal, subgoal,               -- low-level combinators
>                           lambda, can,                 -- introduction rules
>                           done, use, useOp, apply,     -- elimination rules
>                           tyLambda, infr, chk, useTac, -- out of context
>                           switch, cases,               -- dealing with Enum
>                           split,                       -- dealing with Sigma
>                           foldDesc,                    -- dealing with Desc
>                           trustMe,                     -- build terms
>                           setTac, conTac, piTac,
>                           arrTac, (@@@), var           -- brainless shortcuts
>                          ) where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Data.List

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Rules

%endif

The Tactic systems allow us to build well-typed terms from within
Haskell, with relative ease. To do that, we have equipped the |Tac|
data-type with adequate structure, and a set of combinators.

In a first section, we implement |Tac| and dress it up with its
structure. In a second section, we implement the combinators. 

\subsection{The machinery}

A Tactic is something that (might) builds a term of a given type. In
this process, it might be required to create fresh names, hence the
availability of a |NameSupply|. All in all, this goes like this:

> newtype Tac x = Tac { runTac :: NameSupply -> TY -> Either (StackError (Tac VAL)) x }

In other words, we have two @Reader@ monads stacked on an @Error@
monad. I don't know for you but I'm quite happy to reinvent the wheel
by not using the wacky monad transformers. 

\subsubsection{Being monadic}

The corollary is that we have to implement the standard mumbo jumbo
for monads. First, we have a functor:

> instance Functor Tac where
>     fmap f g = Tac { runTac = \r t -> fmap f -- in Either functor
>                                            (runTac g r t) }

Then we have a monad:

> instance Monad Tac where
>     return x = Tac { runTac = \_ _ -> Right x }
>     x >>= f = Tac { runTac = \r t -> 
>                                do -- in Either monad
>                                x <- runTac x r t
>                                runTac (f x) r t }

> instance MonadError (StackError (Tac VAL)) Tac where
>     throwError s = Tac { runTac = \_ _ -> Left s }
>     catchError (Tac f) g = Tac { runTac = \r t -> either (\x -> runTac (g x) r t) Right (f r t) }


\subsubsection{Going |NameSupplier|}

Because a tactic is some sort of |(->) NameSupply|, it is also a
|NameSupply|. Therefore, we abstractly get |freshRef| and |forkSupply|
operations on it. 

Let us work out the implementation:

> instance NameSupplier Tac where
>     askNSupply = Tac { runTac = \supply _ -> Right supply }
>     freshRef x tacF = Tac { runTac = NameSupply.NameSupplier.freshRef x (runTac . tacF) }
>     forkNSupply s child dad = Tac { runTac = \nsupply typ -> 
>                                           do 
>                                           c <- runTac child (freshNSpace nsupply s) typ
>                                           runTac (dad c) (freshName nsupply) typ
>                                }

Which requires |Tac| to be applicative. This is not a trouble now that
we have a monad:

> instance Applicative Tac where
>     pure = return
>     (<*>) = ap

> instance Alternative Tac where
>   empty = throwError' $ err "Alternative empty"
>   s <|> t = catchError s (const t)

\subsection{The tactic combinators}

The combinators are implemented in two layers. In this section, we are
concerned by the lower-level layer: we implement the only combinators
which are allowed to manipulate the inner structure of |Tac {...}|.

This is roughly decomposed in three parts: one to deal with the |TY ->|
part of |Tac|, one to deal with the |NameSupply ->| part, and one to deal
with the Error part. The |NameSupply| aspect might seem poorly equipped:
bear in mind that |Tac| is also |NameSupplier|. Similarly, the Error side
inherits the monadic nature of |Either [String]|.

\subsubsection{Setting goals}

As we have mentioned |TY ->| is a Reader, so are its
combinators. Hence, we can |ask| what is the current type goal with,
well, |goal|. 

> goal :: Tac TY
> goal = Tac { runTac = \nsupply typ -> Right typ }

|subgoal| is the |local| of Reader that runs |tacX| in a local |typ|
environment. Conor is concerned about the fact that, apart from
Inference rules, nobody should be using this guy.

> subgoal :: (TY :>: Tac x) -> Tac x
> subgoal (typ :>: tacX) = 
>     Tac { runTac = \nsupply _ -> 
>             case runTac tacX nsupply typ of
>               Left x -> Left $ (err "subgoal: unable to build an " ++
>                                 err "inhabitant of " ++ errVal typ) : x
>               k -> k
>         }

\subsubsection{Failing, loudly}

When a tactic fails, it is good to know why. So, we provide this
combinator to report a failure.

> failTac :: String -> Tac x
> failTac = throwError' . err

We are not entirely satisfied with this solution, so this will
probably change (for the better) in future iterations. The problem
with this scheme is that you get a stack, consisting of the initial
problem and all its consequences. However, it is often not enough to
pinpoint the precise location of the error. So, this mechanism is
pretty much useless.

\subsection{Syntax-directed tacticals}

Based on the low-level combinators defined in the previous section, we
can build more powerful combinators. In particular, we are interested
in recovering some kind of expressivity: our high-level tactics follow
the syntax of the language, without the cruft (De Bruijn indices,
trivial type checks, \ldots).

This is decomposed in two sections: first, introduction rules, then
elimination rules.

\subsubsection{Introduction rules}

Here is a tip to decipher the types below. The type |Tac VAL| can be
read as "something that will build a well-typed value". I mean, that's
the whole purpose of these tactics, anyway.

The first combinator is our beloved |lambda|. It turns an Haskell
function using a value to \emph{build a well-typed term} into \emph{a
well-typed term builder}. I will stop here with the emphasis, I think
you got the idea now.

> lambda :: (REF -> Tac VAL) -> Tac VAL
> lambda body = do
>   pi <- goal
>   case pi of
>     PI s t ->
>         NameSupply.NameSupplier.freshRef ("" :<: s) $
>                        \x -> do
>                              body <- subgoal (t $$ A (pval x) :>: body x)
>                              discharge x body
>     _ -> failTac $ "lambdaTac: could not match the current goal "
>                    ++ show pi ++ 
>                    " against a Pi type"

The second builder is significantly simpler, as we don't have to care
about binding. Taking a canonical term containing well-typed values,
|can| builds a well-typed (canonical) value. 

To do that, we first ask our goal to live in the canonical
world. That's an obvious requirement. Then, we use an hand-crafted
checker-evaluator |chev| to:

\begin{itemize}
\item Check that |cTac| lives in |t|, and
\item Return the value computed from |cTac|
\end{itemize}

As we are not interested in the original term |x|, we drop it. This
simple operation is a bit noisy because we have defined our own
notation |:=>:| and lack the associated projections.

> can :: Can (Tac VAL) -> Tac VAL
> can cTac = do
>     c <- goal
>     case c of
>       C t -> do
>              v <- canTy chev (t :>: cTac)
>              return $ C $ fmap (\(x :=>: v) -> v) v
>       _ -> failTac $ "can: could not match " ++ show c ++ 
>                      " against a Can type"
>     where chev (t :>: x) = do
>               v <- subgoal (t :>: x)
>               return $ x :=>: v


\subsubsection{Elimination rules}

Elimination rules are manipulating the following type:

> type Use = (VAL :<: TY) -> Tac VAL

Which says something like "provided a value of some inferred type, I
can build a well-typed value, provided that the inferred type meets
our goal". This is used to handle the |In| terms of the language, by
some sort of continuation-passing style construction.

Confirming this intuitive description of |Use|, here is the definition
of |done|. This operator closes the continuation by stopping the guess
work and comparing the inferred type with the current goal.

> done :: Use
> done (v :<: typ) =
>     do
>       typ' <- goal
>       p <- equalR (SET :>: (typ, typ'))
>       case p of 
>         True -> return v
>         False -> failTac $ "done: the provided type " ++ show typ ++
>                            " for value " ++ show v ++ 
>                            " is not equal to the current goal " ++ show typ'
>     where equalR x = do
>             r <- askNSupply
>             return $ equal x r

On the other hand, |apply| builds up the continuation. Provided with
an eliminator |etacX| and a continuation |use|, it builds a
continuation that applies the eliminator to |(x :<: t)|. This
computation is carried by |elimTy| that is provided with an
hand-crafted checker-evaluator |chev|. The role of |chev| is, here, to
simply type-check the arguments of the eliminator. |elimTy| returns
both the reduced eliminator |v| and the result type |tv|. Therefore,
we can simply apply |v| to |x|, and call into |use| with this result
and its type |tv|.

> apply :: Elim (Tac VAL) -> Use -> Use
> apply etacX use (x :<: t) = 
>   case t of
>     C t -> do
>           (v,tv) <- elimTy chev (x :<: t) etacX 
>           let v' = fmap (\(_ :=>: x) -> x) v
>           use (x $$ v' :<: tv)
>     _ -> failTac $ "apply: cannot apply an elimination" ++ 
>                     " on non canonical type " ++ show t
>     where chev (t :>: x) = do 
>             v <- subgoal (t :>: x)
>             return $ x :=>: v


Finally, the continuation is initiated by |use| that, basically,
allows you to apply the term built by |useR| to the |ref|erenced
object, very likely to be a function or any argument of an eliminator
(think, a pair applied to a projection).

To do so, we call the continuation |useR| with the value and type of
|ref|. Then, the continuation machinery will build a grown up term
that, at some point, ends up with a |done|. 

> use :: REF -> Use -> Tac VAL
> use ref useR = 
>     do
>       useR (pval ref :<: pty ref)

Similarly, we can use operators almost transparently with
|useOp|. There are two standard techniques at game here. First, as for
|use|, we set up a continuation to get a |Tac VAL|. Second, as for
|elimTy|, we use |opTy| with a customized checker-evaluator in order
to compute the values of arguments and the result type.

> useOp :: Op -> [Tac VAL] -> Use -> Tac VAL
> useOp op args useR = do
>   (vals, ty) <- opTy op chev args
>   let vs = map (\(_ :=>: v) -> v) vals
>   useR (op @@ vs :<: ty )
>        where chev (t :>: x) = do
>                v <- subgoal (t :>: x)
>                return $ x :=>: v


Hence, we are able to write a standard function application as simply
as:

%if false

> f = undefined
> x1 = undefined
> x2 = undefined

%endif

> example = use f . apply x1 . apply x2 $ done

As for more "complex" examples, here is an identity function:

> ident = lambda (\x -> use x done)
> identT = ARR SET SET

And here is the twice function:

> twice = tyLambda ("X" :<: SET) $ \tx ->
>         let vtx = pval tx in
>         tyLambda ("f" :<: (ARR vtx vtx)) $ \f -> 
>         tyLambda ("x" :<: vtx) $ \x -> 
>         infr $ vtx :>:
>                (use f .
>                 apply (A (use f . 
>                           apply  (A (use x done)) $
>                           done)) $
>                 done)
> twiceT = can $ Pi (can Set)
>                   (lambda $ \x ->
>                    arrTac (arrTac (use x done)
>                                   (use x done))
>                           (arrTac (use x done)
>                                   (use x done)))
> twiceTT = SET

\subsection{Out of context tactics}

Having a |Tac (VAL :<: TY)| at hand is always a good thing. Such a
beast can be reduced to a value, under any goal, because it doesn't
look at the goal to build the value: it is here, on the right. 

To prove that, we proceed by induction: a |Tac (VAL :<: TY)| is either
built from another |Tac (VAL :<: TY)| (see |useTac|, |tyLambda|), or
from a |(TY :>: Tac VAL)|, using |infr|. The base case, |infr|, does
not make use of the current context, as it relies on |subgoal| to
check the value and type it is provided. In the inductive case, the
tactics are not relying on the goal and are only provided
context-independent tactics (by induction hypothesis). Qed.

\pierre{At some point, I think that this should be related to the |Ok|
        tactics, ``the tactics you can always trust'' says the ad.}


Hence, we can implement the typed lambda, for which variable types are
known.

> tyLambda :: (String :<: TY) -> (REF -> Tac (VAL :<: TY))
>                             -> Tac (VAL :<: TY)
> tyLambda (name :<: s) body =
>     NameSupply.NameSupplier.freshRef ("" :<: s) $ \x -> do
>         (vx :<: tx) <- body x -- out of context
>         v <- discharge x vx
>         t <- discharge x tx
>         return $ v :<: PI s t


To build a |Tac (VAL :<: TY)|, we need some help:

> infr :: (TY :>: Tac VAL) -> Tac (VAL :<: TY)
> infr (typ :>: tacX) = do
>     v <- subgoal (typ :>: tacX)
>     return $ v :<: typ

Our efforts are rewarded by the ability to apply an eliminator to a
tactics, and get a typed tactics back:

> useTac :: Tac (VAL :<: TY) -> Elim (Tac VAL)
>                            -> Tac (VAL :<: TY)
> useTac tacf etacx = do
>     (v :<: t) <- tacf  -- out of context
>     case t of
>       C tv -> do
>               (e,t) <- elimTy chev (v :<: tv) etacx
>               let e' = fmap (\(_ :=>: v) -> v) e
>               return $ v $$ e' :<: t
>       _ -> failTac $ "useTac: inferred type " ++
>                       show t ++ " is not a Constructor"
>     where chev (t :>: x) = do
>             v <- subgoal (t :>: x)
>             return $ x :=>: v

At last, we can get a normal tactics out of typed one, with a bit of
checking:

> chk :: Tac (VAL :<: TY) -> Tac VAL
> chk tacVT = do
>   (v :<: t) <- tacVT -- out of context
>   done $ v :<: t


\subsection{Building functions on |EnumT|}

The code below is a work in progress. It should work fine if you use
it well, but will fail badly if you don't. We (Conor and Pierre) are
currently working on an improved tactics system that would give
stronger guarantees. This would affect the code below but also the code
above: it's more of a make-over than a refactoring. An example of sin
is the generalized usage of |subgoal|: in theory, |subgoal| should be
limited to inference rules. Therefore, it should disappear from this
code, at some point.

The following tactic aims at automating as much as possible the
implementation of function operating on finite enumerations. Such
functions have a type |Pi (EnumT e) P|. Therefore, when facing such a
goal, we create a lambda that gives us an |x| in |EnumT e|. To build
the expected |P x|, we rely on |switchOp|. The argument |ps| of
|switchOp| corresponds to the result for each case of the enumeration.

> switch :: Tac VAL -> Tac VAL
> switch cases = do
>     t <- goal
>     case t of
>       PI (ENUMT e) p ->
>           lambda $ \x -> do
>           useOp switchOp [ return e
>                          , use x done
>                          , return p
>                          , cases ] done
>       _ -> failTac $ "switch: current goal is " ++
>                        show t ++ " when a Pi (EnumT e) was expected"

To build the result cases, we use the following |cases|
combinator. Each case of the enumeration must be addressed, in order,
by a list of tactics. We simply build a tuple which satisfies the
|branchesOp e P| type and can be fed to |switchOp|.

> cases :: [Tac VAL] -> Tac VAL
> cases [] = can Void
> cases (p:ps) = can $ Pair p (cases ps)

Here is a trivial example. We define the enumeration $\{1,2,3,4\}$:

> test1234 :: VAL
> test1234 = ENUMT (CONSE (TAG "1") 
>                   (CONSE (TAG "2")
>                    (CONSE (TAG "3")
>                     (CONSE (TAG "4")
>                      NILE))))

And we implement the function that permutes each element $i$ to $5-i$:

> perm = switch $ cases [ return (TAG "4"),
>                         return (TAG "3"),
>                         return (TAG "2"),
>                         return (TAG "1") ]
>
> permT :: TY
> permT = ARR test1234 test1234

\subsection{Splitting on Sigmas}

Here is the eliminator for Sigmas:

> split :: Tac VAL -> Tac VAL
> split tacF = do
>   t <- goal
>   case t of
>     PI (SIGMA a b) t -> 
>          lambda $ \x -> do
>            useOp splitOp [ return a
>                          , return b
>                          , use x done 
>                          , return t
>                          , tacF ] done
>     _ -> failTac $ "split: current goal is " ++
>                     show t ++ " but expected a Pi (Sigma . .) ."

\pierre{I should tell a story above.}

\subsection{Eliminating Descs}

Same thing here, for the |Mu| eliminator:

> foldDesc :: Tac VAL -> Tac VAL
> foldDesc p = do
>   t <- goal
>   case t of 
>     PI (MU l d) bp ->
>         lambda $ \v ->
>             useOp elimOp [ return d
>                          , use v done 
>                          , return bp
>                          , p ] done
>     _ -> failTac $ "foldDesc: current goal is " ++
>                     show t ++ " but expected a Pi (Mu .) ."
>     

\pierre{I should tell a story above, too.}

\pierre{I should also come up with a general scheme for eliminators:
        if you have seen Switch, Split, and Fold, you know that
        something is happening.}


\subsection{Using |Tac|}

At some point, we need to build a value. Here is the place where it is
done. We trust you to provide |trustMe| with a correct type,
corresponding to the type of the value built by the |Tac VAL|. If it
doesn't, good luck to find the mistake.

> trustMe :: (TY :>: Tac VAL) -> VAL
> trustMe (typ :>: tacV) = 
>     case runTac tacV (B0 :< ("tactics",0),0) typ of
>       Left e -> error $ "Something bad happened." -- concat $ intersperse "\n" $ reverse e
>       Right x -> x



\subsection{Some handy combinators}

The following combinators are brain-less shortcuts. There is nothing
really exciting about that. Just that they exist.

> setTac :: Tac VAL
> setTac = can Set
>
> conTac :: Tac VAL -> Tac VAL
> conTac t = can $ Con t
>
> piTac :: Tac VAL -> (REF -> Tac VAL) -> Tac VAL
> piTac s t = can $ Pi s (lambda t)
>
> arrTac :: Tac VAL -> Tac VAL -> Tac VAL
> arrTac s t = piTac s (\_ -> t)
>
> (@@@) :: REF -> [Tac VAL] -> Tac VAL
> f @@@ xs = foldl' app (use f) xs $ done
>     where app f x = f . apply (A x)
>
> var :: REF -> Tac VAL
> var r = use r done
