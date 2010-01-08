%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Elimination where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable hiding (sequence_)
> import Data.List
> import Data.Traversable hiding (sequence)

> import BwdFwd
> import Developments
> import Naming
> import PrettyPrint
> import Root
> import Rooty
> import Rules
> import Tm
> import ProofState

> import MissingLibrary

> import Debug.Trace

%endif

\section{Elimination with a Motive}

Elimination with a motive works on a goal prepared \emph{by the user} in the
following form:

$$\Gamma, \Delta \vdash ? : T$$

Where $\Gamma$ are the external hypotheses, $\Delta$ the internal hypotheses,
and $T$ the goal to solve. The distinction between \emph{internal} and
\emph{external} hypotheses comes from the use of these hypotheses in the
motive, that is the parameterization of the subproblems on the internal
hypotheses, whereas the external hypotheses will scope over all subproblems at
once.

Note that, given a |ProofState|, we need a way to identify where to chunk the
context into its $\Gamma$ and $\Delta$ parts. One way to do that is to ask the
user to pass in the reference to the first term of $\Delta$ in the context. If
the user provides no reference, we will assume that $\Gamma$ is empty, hence
that the hypotheses are all internal:

< elim :: Maybe REF -> (...)

Obviously, we also need to be provided the eliminator we want to use. Again,
we expect the user to prepare the eliminator for us, in the same context:

$$\Gamma, \Delta \vdash e : (P : \Xi \rightarrow *) 
                            \rightarrow \vec{m} 
                            \rightarrow P \vec{t}$$

Therefore, this eliminator is handled to the elimination machinery using a
|REF|:

< elim :: Maybe REF -> REF -> ProofState ()
< elim comma eliminator = (...)

\subsection{Analyzing the eliminator}

Presented as a development, |elim| is therefore called in the following
context:

\begin{center}
\begin{alltt}
[ \((\Gamma)\) \(\rightarrow\) 
  \((\Delta)\) \(\rightarrow\)
] := ? : T
\end{alltt}
\end{center}

To analyze the eliminator, we play a nice game. One option could be to jump in
a |draftModule|, introduce |lambdaBoys|, and retrieve the different parts as
we go along. However, this means that the terms we get are built from
references which will become out of context, hence invalid. Therefore, we
suffer the burden (and danger) of carrying renaming of those terms.

The way we actually go is the following. The trick consists in re-building the
eliminator in the current development:

\begin{center}
\begin{alltt}
[ \((\Gamma)\) \(\rightarrow\) 
  \((\Delta)\) \(\rightarrow\)
  h [   \(P' \rightarrow\)
        \(m\sb{1} \rightarrow\)
        (...)
        \(m\sb{n} \rightarrow\)
        P := ? : \(\Xi \rightarrow *\)
        \(m\sb{1}\) := ? : \((P : \Xi \rightarrow *) \rightarrow *\)
        (...)  
        \(m\sb{n}\) := ? : \((P : \Xi \rightarrow *) \rightarrow *\)
    ] := e P \(\vec{m}\) : P \(\vec{t}\)
] := ? : T
\end{alltt}
\end{center}

Therefore, we will build the motive \emph{in-place}, instead of analyzing the
eliminator and then making the motive in two phases.

The development transformation is achieved by the following code:

> introElim :: REF -> ProofState [INTM]
> introElim e@(_ := _ :<: eType) = do
>     -- Jump in a girl (oh!) to chunk (and access) 
>     -- the types of the eliminator
>     eTypeTm <- bquoteHere eType
>     make $ "h" :<: eTypeTm
>     goIn
>     -- Get the type of the motive
>     p' <- lambdaBoy "(P)"
>     -- Get the type of the methods
>     ms' <- many $ lambdaBoy "(m)"
>     -- Check the motive, methods, and target shape
>     checkMotive p'
>     checkMethods p' ms'
>     checkTarget p'
>     -- Politely ask for making a real motive
>     -- We will build it, no worry
>     pTyTm <- bquoteHere $ pty p'
>     p <- make $ "P" :<: pTyTm
>     -- Politely ask for making real methods
>     -- These ones are up to the user
>     mTyTms <- sequence $ map (bquoteHere . pty) ms'
>     ms <- sequence $ map (\m -> make $ "m" :<: m) mTyTms
>     -- Close the problem (Using the "made" subproblems!)
>     -- And goes to the next subproblem, ie. making P
>     giveNext $ N $ P e $## (p : ms)
>     return ms

The call to |checkMotive|, |checkMethods|, and |checkTarget| are here to
ensure that we are handed ``stuffs´´ which fit our technology. They are dull
at the moment, because we only have nice users.

|checkMotive| consists in veryfing that the motive is of type:

$$P : \Xi \rightarrow *$$

|checkMethods| consists in verifying that the methods are of type:

$$(P : \Xi \rightarrow *) \rightarrow *$$

On the other hand, |checkTarget| consists in verifying that the target
consists of the motive applied to some stuffs.

\pierre{There are also some conditions on the variables that can be used in
these terms! I have to look that up too. This is a matter of traversing the
terms to collect the |REF|s in them and check that they are of the right
domains.}

> checkMotive :: REF -> ProofState ()
> checkMotive p =
>     trace "Hi, it's Elim. I assume your motive is motivating." $
>     return ()
>
> checkMethods :: REF -> [REF] -> ProofState ()
> checkMethods p methods = 
>     trace "Hi, it's Elim. I assume your methods are methodic." $
>     return ()
>
> checkTarget :: REF -> ProofState ()
> checkTarget p = 
>     trace "Hi, it's Elim. I assume your target is tasty." $ do
>     goal <- getGoal "checkTarget" 
>     return ()

\subsection{Making the motive}

The |introElim| command have kindly generated a subgoal for the motive as well
as subgoals for the methods. Doing that, it has also brought us to the subgoal
consisting of making |P|. That's a good think because this is what we are
going to do.

First, remember the type of the motive:

$$P : \Xi \rightarrow *$$

So, we can introduce these lambdas straight away:

> introMotive :: ProofState [REF]
> introMotive = do
>     xis <- many $ lambdaBoy "xi"
>     return xis              

Now the question is: what term are we supposed to build? To answer that
question, we read the Sanctified Paper \cite{mcbride:motive}. What we have to
build is this:

$$
\lambda \overrightarrow{(xi : \Xi))} \rightarrow
    \overrightarrow{(d : \Delta))} \rightarrow
    \overrightarrow{\vdash xi == d} \Rightarrow
    T
$$

\pierre{Before introducing the |Pi|s in the solution, we should try to
simplify the motive. This is not done at the moment.}

Hence, first, we have to introduce the internal context:

> introInternalCtxt :: [INTM] -> ProofState [REF]
> introInternalCtxt ctxt = do
>     deltas <- sequence $ 
>               map (\t -> piBoy ("delta" :<: t)) ctxt
>     return deltas                

Then, we make the equalities between the arguments of the motive and the
internal context:

> mkEqualities :: [(REF,REF)] -> [VAL]
> mkEqualities = map mkEquality
>     where mkEquality (xi, delta) 
>              = PRF (EQBLUE (pty xi :>: NP xi) (pty delta :>: NP delta))

At this stage, we just have to finish up the work by making the term. This
consists in chaining the equalities, and ending with the goal:

> mkTerm :: [VAL] -> VAL -> VAL
> mkTerm equalities goal = Data.List.foldr ARR goal equalities

And we will just have to "give" that term when we are ready.

Finally, we can make the motive, that is close that subgoal. This simply
consists in chaining the commands above, and give the computed term. Unless
I've screwed up things, |give| should always be happy.

> makeMotive :: VAL -> [REF] -> ProofState INTM
> makeMotive goal deltas = do
>     -- Gets the arguments in $\Xi$
>     xis <- introMotive  
>     -- Makes the body
>     -- Starting with |Pi|s on $\Delta$
>     deltasTy <- sequence $ map (bquoteHere . pty) deltas
>     deltas <- introInternalCtxt deltasTy
>     -- Then, make the body of the term
>     let constraints = mkEqualities $ zip xis deltas
>     let motive = mkTerm constraints goal
>     -- And give it
>     motive <- bquoteHere motive
>     give motive

\subsection{Applying the motive}

Remember our eliminator:

$$\Gamma, \Delta \vdash e : (P : \Xi \rightarrow *) 
                            \rightarrow \vec{m} 
                            \rightarrow P \vec{t}$$

We now have built the following motive |P|:

$$
\lambda \overrightarrow{(xi : \Xi))} \rightarrow
    \overrightarrow{(d : \Delta))} \rightarrow
    \overrightarrow{\vdash xi == d} \Rightarrow  
    T
$$

And we have introduced the methods $\vec{m}$, letting the user the task to
solve these subgoals. Hence, we can apply the eliminator, which will result in
a function of the following type:

$$
P \vec{t} \equiv \overrightarrow{(d : \Delta))} \rightarrow
                 \overrightarrow{\vdash xi == d} \Rightarrow  
                 T
$$

That is, we need to apply the result of |elim motive methods| to the internal
context $\Delta$ and the reflexivity proofs.

Let us build these proofs first. This simply consists in taking each variable
in $\Delta$ and apply |refl| to it.

> mkRefls :: [REF] -> Root -> [INTM]
> mkRefls deltas r = map mkRefl deltas
>     where mkRefl delta = N $ (P refl) $## [ bquote B0 (pty delta) r
>                                           , NP delta ]

Then, it is straightforward to build the term we want and to give it:

> applyElim :: REF -> INTM -> [INTM] -> [REF] -> ProofState ()
> applyElim elim motive methods deltas = do
>     reflDeltas <- withRoot (mkRefls deltas)
>     giveSilently $ N $ (P elim) $## (motive : 
>                                      methods ++
>                                      (map NP deltas) ++
>                                      reflDeltas)

We (in theory) have solved the goal!

\subsection{Putting things together}

Here we go. In a first part, we need to retrieve some information about our
goal and its context. 

> elimContextGoal :: ProofState ([REF], VAL)
> elimContextGoal = do
>     -- The motive needs to know our goal
>     (_ :=>: goal) <- getGoal "T"
>     -- Lacking a comma term, we assume that 
>     -- the whole context is internal
>     deltas <- getBoys 
>     return (deltas, goal)

In a second part, we turn the eliminator into a girl and play the doctor with
her: we look at her internals, check that everything is correct, and make
sub-goals. Note that |introElim| make a girl and we carefully |goOut| her in
|elimDoctor|.

> elimDoctor :: [REF] -> VAL -> REF -> ProofState (INTM, [INTM])
> elimDoctor deltas goal eliminator = do
>     -- Prepare the development by creating subgoals:
>     --    1/ the motive
>     --    2/ the methods
>     methods <- introElim eliminator
>     -- Build the motive
>     motive <- makeMotive goal deltas
>     -- Leave the development with the methods unimplemented
>     goOut
>     return (motive, methods)

In a third part, we solve the problem. To that end, we simply have to use the
|applyElim| command we have developed above.

Therefore, we get the |elim| commands, the one, the unique. It is simply a
Frankenstein operation of these three parts:

> elim :: Maybe REF -> REF -> ProofState ()
> elim Nothing eliminator = do -- Nothing: no comma
>     -- Where are we?
>     (deltas, goal) <- elimContextGoal
>     -- What is the eliminator?
>     (motive, methods) <- elimDoctor deltas goal eliminator
>     -- Apply the motive, ie. solve the goal
>     applyElim eliminator motive methods deltas



A small function to retrieve our scope. This might as well go in
@ProofState@ if this is sufficiently useful:

> getBoys = do  
>     auncles <- getAuncles
>     return $ foldMap boy auncles 
>    where boy (E r _ (Boy _) _)  = [r]
>          boy _ = []
