%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.Induction where

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import DisplayLang.DisplayTm

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.Edition.ProofState
> import ProofState.Interface.ProofKit

> import DisplayLang.Naming

%endif

\section{Induction on |Desc|}

This machinery aims at making the life with |Desc| easier. Whereas
|Desc| comes with a generic eliminator, |elimOp|, solving the computed
subgoal is often a nightmare. Indeed, the subgoal has the following
shape:

$$(x : \mbox{descOp}(D,\mbox{Mu} D)) \rightarrow 
  (y : \mbox{boxOp}(D, \mbox{Mu} D, P, x)) -> 
  P (\mbox{con} x)$$

I will arbitrarily call the content of |x| the \emph{data}, and the
content of |y| the \emph{hypotheses}. By definition of |descOp| and
|boxOp|, the data and the hypotheses are stored into some ugly dependent
record. 

The purpose of the following code is to unpack these things, and get
rid of the junk (such as the empty record, for instance). To operate,
we simply need to be provided the description on which we are doing
the induction. By reading that description, we flatten the goal and/or
chunk it up in smaller sub-goals.


\subsection{Some Kit}

First of all, let us implement some piece of generic machinery. Both
functions have a similar role: facing a particular proof goal, they
synthesize an equivalent but "nicer" goal and close the first one with
the synthesized one. 

\pierre{This code can be moved somewhere else, and even
renamed. Moreover, these two functions are duplicating the behavior of
|elaborate| for |PI UNIT T| and |PI (SIGMA A B) T|. I am not really
tempted to merge these two things (by fear of breaking things) but if
someone feels like it, go ahead.}

Hence, |eatUnit| will simplify a proof goal |UNIT -> T| into a goal
|T'|. Note the presence of an |action|, executed in context of the
subgoal. This allows further simplifications on the subgoal.

> eatUnit :: ProofState () -> TY -> ProofState ()
> eatUnit action (PI UNIT _T) = do
>     -- Synthesize the new goal |T|
>     _TVoidtm <- bquoteHere (_T $$ A VOID)
>     (t :=>: _) <- make $ "t" :<: _TVoidtm
>     -- Potentially, act on it
>     goIn 
>     action
>     goOut
>     -- Solve the first goal
>     give' $ L $ K (N t)
>     return ()
> eatUnit _ e = 
>     throwError' $  err "eatUnit: expecting a (Sig () -> T)," 
>                    ++ err " got a " 
>                    ++ errVal e

Similarly, the function |unpackSigma| turns a goal |Sig (A ; B) -> T|
into a goal |(a : A)(b : B a) -> T'|. 

> unpackSigma :: ProofState () -> TY -> ProofState ()
> unpackSigma action (PI (SIGMA _A _B) _T) = do
>   -- First, the type of the new goal
>   let newGoal = PI _A . L . HF (fortran _B) $ \ a ->
>                 PI (_B $$ A a) . L . HF (fortran _T) $ \ b ->
>                 _T $$ A (PAIR a b)
>   -- Synthesize the new goal
>   _TPiTm <- bquoteHere newGoal
>   (t :=>: _) <- make $ "t" :<: _TPiTm
>   -- Potentially, act on it
>   goIn
>   action
>   goOut
>   -- Solve the first goal
>   ab <- lambdaBoy "ab"
>   give' $ N (t  :$ A (N (P ab :$ Fst))
>                 :$ A (N (P ab :$ Snd)))
>   return ()
> unpackSigma _ e = throwError' $ err "unpackSigma: expecting a (Sig (A ; B) -> T)," 
>                                 ++ err " got a " 
>                                 ++ errVal e




\subsection{Grabbing the data}

Let us recall one more time the shape of the goal:

$$(x : \mbox{descOp}(D,\mbox{Mu} D)) \rightarrow 
  (y : \mbox{boxOp}(D, \mbox{Mu} D, P, x)) -> 
  P (\mbox{con} x)$$

In this section, we flatten the data part, that is a 
$(x : \mbox{descOp}(D,\mbox{Mu} D))$. 

Doing that, we actually walk through the description as a tree, with
|DONE| as leaves. For each kind of node, the record takes a specific
form. Knowing at which node we are, we can, first, flatten the data at
the current node and, second, move downward in the record.

A difficulty arises with |ARG|. Let us look at the interpretation of
|ARG X F|:

< descOp(ARG X F, Mu D) = Sigma X (\x -> descOp(F x, Mu D))

Because the |Sigma| is used in a truely dependent maneer, |X| has the
ability to modify the subsequent structure of the record. Hence, once
we have reached a |DONE| leaf, it is non trivial to know through which
nodes we have gone through: it depends on the choice of |x : X| we
have made. We will keep track of this path using the following
data-type, accumulated in |Bwd| list:

> data Branch = ReadArg
>             | ReadInd

Implicity, the |B0| of a |Bwd Branch| is taken as a |ReadDone|.


Let us introduce the data part now. As mentionned above, we accumulate
the path in a |Bwd Branch| while walking over the description,
provided here as a |VAL|.

> introData :: Bwd Branch -> VAL -> ProofState ()

\paragraph{First case: |DONE|}

By definition of |descOp|, we have:

< descOp(DONE, Mu D) = Unit

Meaning that the goal has the following shape:

$$(x : Unit) \rightarrow 
  (y : \mbox{box}(D, \mbox{Mu} D, P, x)) -> 
  P (\mbox{con} x)$$

Trivially, we can eat the unecessary |Unit|, using |eatUnit|. Much
less trivially, we notive that the next |Pi|s corresponds to the
hypotheses: we trigger the |introHyps| code we will develop in the
next part. Intuitively, |introHyps| reads the history to flatten the
hypotheses part.

If you trust me on |introHyps|, at the end of that transformation, we
have computed the entirely flattened goal. 

\pierre{I admit that presenting |DONE| in a first step is a bit
counter-intuitive. We kind of start with the end. However, it is the
simplest in term of data flattening.}

> introData branch DONE = 
>   withGoal $ 
>   -- Eat the Unit prefix
>   eatUnit $ 
>   -- Flatten the hypothesis part
>   introHyps branchFwd
>       where branchFwd = branch <>> F0


\paragraph{Second case: |IND1|}

By definition of |descOp|, we have:

< descOp(IND1 D', Mu D) = TIMES (Mu D) descOp(D', Mu D)

So, to flatten this record, we first need to unpack the components of
this non-dependent |Sigma|. Then, we can bring the element of |Mu D|
in the context: this is flattened data. Finally, we recursively
flatten the structure made by the interpretation of |D'|.

> introData branch (IND1 _D') = 
>   withGoal $ 
>   unpackSigma $ do
>                 -- Bring (x : Mu D) in context
>                 lambdaBoy "x"
>                 -- Flatten the subsequent record
>                 introData (branch :< ReadInd) _D'
>                 return ()


> introData branch (IND _H _D') = 
>   withGoal $ 
>   unpackSigma $ do
>                 -- Bring (xh : H -> Mu D) in context
>                 lambdaBoy "xh"
>                 -- Flatten the subsequent record
>                 introData (branch :< ReadInd) _D'
>                 return ()




> introData branch (ARGF _X _F) = do
>   withGoal $ unpackSigma $ do
>     (_ :=>: goal) <- getGoal "introData:Done 2"
>     case goal of
>       PI _ _T -> do
>                  _Xtm <- bquoteHere _X
>                  _Ttm <- bquoteHere _T
>                  branches <- bquoteHere $ branchesOp @@ [_X, _T]
>                  (m :=>: _) <- make $ "branches" :<: branches
>                  goIn
>                  (_ :=>: goal) <- getGoal "introData:Done 3"
>                  cases <- mkCases (branch :< ReadArg) ZE goal (\n -> switchOp @@ [_X, n, L (K desc), _F])
>                  give' $ cases
>                  goOut
>                  x <- lambdaBoy "x"
>                  give' $ N $ switchOp :@ [ _Xtm, NP x, _Ttm, N m ]
>                  return ()

> introData branch (ARG _X _F) = do
>   withGoal $ unpackSigma $ do
>     x <- lambdaBoy "x"
>     introData (branch :< ReadArg) (_F $$ A (NP x))
>     return ()
            





> mkCases :: Bwd Branch -> VAL -> VAL -> (VAL -> VAL) -> ProofState INTM
> mkCases _ _ UNIT _F = return VOID
> mkCases branch n (TIMES goal t) accF = do
>   goalTm <- bquoteHere goal
>   subgoalTm :=>: subgoal <- make $ "case" :<: goalTm
>   goIn 
>   introData  branch (accF n)
>   goOut 
>   cases <- mkCases branch (SU n) t accF
>   return $ PAIR (N subgoalTm) cases
> mkCases _ t v _ = error $ "mkCases: " ++ show t ++ "\n" ++ show v


\subsection{Knowing your History, making hypotheses}



> introHyps :: Fwd Branch -> ProofState ()

> introHyps F0 = withGoal $ eatUnit $ return ()

> introHyps (ReadInd :> bs) = do
>     withGoal $ unpackSigma $ do
>       lambdaBoy "Px"
>       introHyps bs

> introHyps (ReadArg :> bs) = do
>   introHyps bs



\subsection{Selling your soul to the Cochon}


> induction :: RelName -> ProofState ()
> induction desc = do
>     _D <- resolveDiscard desc
>     case _D of 
>       _ := (DEFN (MU _ v) :<: _) -> do
>                    introData B0 v
>                    nextGoal
>       _ -> throwError' $ err "induction: undefined Desc"

> import -> CochonTactics where
>   : (unaryNameCT  "induction"
>                   (\name -> induction name >> return "Simplification done.")
>       "induction <Desc> - simplify the result of an elimination on a Desc.")
