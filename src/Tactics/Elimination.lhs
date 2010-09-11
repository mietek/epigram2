\section{Elimination with a Motive}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternGuards #-}

> module Tactics.Elimination where

> import Prelude hiding (elem)

> import Control.Applicative
> import Control.Monad
> import Data.Foldable
> import Data.List hiding (elem)
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Name
> import ProofState.Interface.Module
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Lifting
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import ProofState.Interface.Solving

> import DisplayLang.Name



%endif


Elimination with a motive works on a goal prepared \emph{by the user} in the form
$$\Gamma, \Delta \vdash ? : T$$
where $\Gamma$ is the list of external hypotheses, $\Delta$ is the list of internal
hypotheses and $T$ is the goal to solve. The difference between external
and internal hypotheses is the following. External hypotheses scope
over the whole problem, that is the current goal and later
sub-goals. They are the ``same'' in all subgoals. On the other hand,
internal hypotheses are consumed by the eliminator, hence are
``different'' in all subgoals.

We need a way to identify where to divide the context into $\Gamma$ and
$\Delta$. One way to do that is to ask the user
to pass in the reference to the first term of $\Delta$ in the
context. If the user provides no reference, we will assume that
$\Gamma$ is empty, so the hypotheses are all internal.

Obviously, we also need to be provided the eliminator we want to use.
We expect the user to provide the eliminator for us in the form
$$\Gamma, \Delta \vdash e : (P : \Xi \rightarrow \Set) 
                            \rightarrow \vec{m} 
                            \rightarrow P \vec{t}$$
where we call $P$ the \emph{motive} of the elimination, $\Xi$ the
\emph{indices}, $\vec{m}$ the \emph{methods}, $\vec{t}$ the \emph{targets}
and $P \vec{t}$ the \emph{return type}.

We will define |elim| this way:

< elim :: Maybe REF -> (TY :>: INTM) -> ProofState ()
< elim comma eliminator = (...)




\subsection{Analyzing the eliminator}
\label{subsec:Tactics.Elimination.analysis}

Presented as a development, |elim| is called in the context
\begin{center}
\begin{minipage}{5cm}
\begin{alltt}
[ \((\Gamma)\) \(\rightarrow\) 
  \((\Delta)\) \(\rightarrow\)
] := ? : T
\end{alltt}
\end{minipage}
\end{center}
where $\Gamma$ and $\Delta$ are introduced and |T| is waiting to be solved.

We have to analyze the eliminator we are given for two reasons. First,
we need to check that it \emph{is} an eliminator, that is:
\begin{itemize}
\item it has a motive,
\item it has a bunch of methods, and
\item the target consists of the motive applied to some arguments.
\end{itemize}
Second, we have to extract some vital pieces of information from the
eliminator, namely:
\begin{itemize} 
\item the type $\Xi \rightarrow \Set$ of the motive, and
\item the targets $\vec{t}$ applied to the motive.
\end{itemize}

To analyze the eliminator, we play a nice game. One option would be to
jump in a |draftModule|, introduce |lambdaParam|s, then retrieve and
check the different parts as we go along. However, this would mean that the
terms would be built from references that would become invalid when the
draft module was dropped. Therefore, we would suffer the burden (and danger)
of manually renaming those references.

The way we actually proceed is the following. The trick consists of
rebuilding the eliminator in the current development:

\begin{center}
\begin{minipage}{6cm}
\begin{alltt}
[ \((\Gamma)\) \(\rightarrow\) 
  \((\Delta)\) \(\rightarrow\)
  makeE [   P := ? : \(\Xi \rightarrow Set\)
            \(m\sb{1}\) := ? : \(M\sb{1}\) P
            (...)  
            \(m\sb{n}\) := ? : \(M\sb{n}\) P
  ] := e P \(\vec{m}\) : P \(\vec{t}\)
] := ? : T
\end{alltt}
\end{minipage}
\end{center}

We will build the motive \emph{in-place}, instead of
analyzing the eliminator \emph{and then} making the motive. Moreover,
we are able to safely check the shape of the eliminator and
extract the interesting bits.

The |introElim| command takes the eliminator with its type, which should be a
function whose domain is the motive type and whose range contains the methods
and return type. It creates a new definition for the rebuilt eliminator, with
subgoals for the motive and methods. It returns the name of the rebuilt
eliminator, the motive type and the list of targets; the cursor is left on
the motive subgoal.

> introElim :: (TY :>: EXTM) -> ProofState (Name, TY, Bwd INTM)
> introElim (PI motiveType telType :>: elim) = do

Make a module, which we will convert to a goal of type $P \vec{t}$ later:

>     elimName <- makeModule "makeE"
>     goIn

Make a goal for the motive:

>     motiveTypeTm           <- bquoteHere motiveType
>     -- telTypeTm              <- bquoteHere telType
>     motive :=>: motiveVal  <- make $ "motive" :<: motiveTypeTm

Make goals for the methods and find the return type:

>     (methods, returnType) <- makeMethods B0 (telType $$ A motiveVal)

Check motive and grab the targets (the terms that are applied to it):

>     targets <- checkTargets returnType motiveType (motiveVal :<: motiveType)

Convert the module to a goal, solve it (using the subgoals created above)
and go to the next subproblem, i.e. making the motive $P$:

>     moduleToGoal returnType
>     give $ N $ elim :$ A (N motive) $## methods
>     goIn
>     goTop
>     return (elimName, motiveType, targets)


If the eliminator is not a function from motive and methods to return type, there
is nothing we can do:

> introElim _ = throwError' $ err "elimination: eliminator not a pi-type!"


\subsubsection{Making the methods}

Above, we have used |makeMethods| to introduce the methods and retrieve
the return type of the eliminator. Remember that the eliminator is a
telescope of $\Pi$-types. To get the type of the motive, we have
matched the first component of the telescope. To get the methods, we
simply iterate that process, up to the point where all the $\Pi$s have
been consummed.

> makeMethods :: Bwd INTM -> TY -> ProofState (Bwd INTM, INTM)
> makeMethods ms (PI s t) = do
>     sTm        <- bquoteHere s
>     m :=>: mv  <- make $ "method" :<: sTm
>     makeMethods (ms :< N m) (t $$ A mv)
> makeMethods ms target = do
>     targetTm <- bquoteHere target
>     return (ms, targetTm)


\subsubsection{Checking the motive and targets}

The |checkTargets| command verifies that the motive is of type
$\Xi \rightarrow Set$ and that the return type is the motive applied to
some arguments (the targets), which are returned.

> checkTargets :: INTM -> VAL -> (VAL :<: VAL) -> ProofState (Bwd INTM)
> checkTargets returnType SET (motive :<: motiveType) = do
>      isEqual <- withNSupply $ equal (motiveType :>: (evTm returnType, motive))
>      if isEqual 
>          then return B0
>          else throwError' $ err "elimination: return type does not use motive!"
> checkTargets (N (f :$ A x)) (PI s t) (motive :<: motiveType) =
>     freshRef ("s" :<: s) $ \s -> do
>         xs <- checkTargets (N f) (t $$ (A $ pval s)) (motive :<: motiveType)
>         return (xs :< x)
> checkTargets _ _ _ = throwError' $ err "elimination: your motive is suspicious!"

\pierre{There are also some conditions on the variables that can be used in
these terms! I have to look that up too. This is a matter of traversing the
terms to collect the |REF|s in them and check that they are of the right
domains.}
\question{Do these conditions actually matter?}



\subsection{Identifiying the motive}

The |introElim| command has generated a subgoal for the motive and left us inside
it. That's a good thing because this is what we are going to do.


\subsubsection{Overview}

Now the question is: what term are we supposed to build? To answer
that question, the best is still to read the Sanctified Papers
\cite{mcbride:motive, mcbride:pattern_matching}. If you can bear with
me, here is my strawman explanation.


\paragraph{First try: life's too short, the paper's too long.}

Remember that the eliminator will evaluate to the following term:

$$P \vec{t}$$

So, we could define $P$ as:

$$P \equiv \lambda (\Xi) . T$$


Which trivially solves the goal. However, we will have a hard time
making the methods! Indeed, we are asking to solve exactly the same
problem, with the same knowledge.


\paragraph{Second try: learning from the targets.}


We need to hand back some knowledge to the user in the methods. Where
could any knowledge come from? Well, we are sure of one thing: $(\Xi)$
will be instantiated to $\vec{t}$. So, we could define our motive as:

$$P \equiv \lambda (\Xi) . (\Xi) == \vec{t} \Rightarrow T$$

Hence, the methods will have some additional knowledge, presented as
constraints on the value that their arguments can take.


\paragraph{Third try: the problem with inductive eliminators.}


This definition would work for the ''non-inductive'' eliminators, that
is eliminators for which the method types are all of the following
form:

$$M P \equiv \Pi \Delta_S \rightarrow P \vec{s}$$

These eliminators are simply doing a case analysis, without refering
to an induction principle.

However, for ``inductive'' eliminators, this motive is too weak. An
eliminator will be inductive-ish if a method is using the motive
anywhere else than as a target. If this is the case, we would like to
be able to appeal to some induction principle: we need the freedom to
apply the motive in another context than the fixed context
$\Delta$. We can get this by abstracting $\Delta$ in $P$, without
forgetting to bring $\vec{t}$ and $T$ under this new context:

$$P \equiv \lambda (\Xi) . \Pi (\Delta') .
     (\Xi) == \vec{t}\ [\Delta'/\Delta] \Rightarrow T[\Delta'/\Delta]$$



\paragraph{Fourth try: being less parametric.}

However, there is a slight problem here. The motive and the methods
are very likely to be parameterized over $\Delta$. If we use the
motive above, we are asking for trouble in the definition of the
methods. Remember that a method typically looks like:

$$M P \equiv \Pi \Delta_S \rightarrow P \vec{s}$$

This will therefore compute to:

$$\Pi \Delta_S \Pi \Delta \Rightarrow
     \vec{s} == \vec{t}\ [\Delta'/\Delta] \Rightarrow 
     T[\Delta'/\Delta]$$

The effect is therefore that this type becomes more parametric than it
was before, for no good reason. Indeed, there is no way a method can
take advantage of this parametricity: it will be used as a boring
parameter (because it \emph{is} just a parameter).

So, we need to chunk $\Delta$ in two contexts:

\begin{itemize}

\item $\Delta_0$, containing terms involved in the type of the methods
and motive, and their respective dependencies; and

\item $\Delta_1$, containing the free terms

\end{itemize}

Instead of brutally abstracting over $\Delta$, we subtly abstract over
$\Delta_1$:

$$P \equiv \lambda (\Xi) . \Pi (\Delta_1') .
     (\Xi) == \vec{t}\ [\Delta_1'/\Delta_1] \Rightarrow T[\Delta_1'/\Delta_1]$$



\paragraph{Fifth try: simplifying equations.}

Although the previous version would be morally correct, the user will
appreciate if we simplify some trivial equations by directly
instantiating them. Our motto being ``the user is king'' (don't quote
me on that), let's simplify.

Hence, if we have $\xi_i : \Xi_i == t_i : T_i$ with $\Xi_i == T_i$ and
$t_i$ a term defined in the context $\Delta_1'$, then we can replace
$t_i$ by $\xi_i$ everywhere it appears, in the telescope and in the
goal. Having replaced $t_i$, we can remove the corresponding
abstraction in the telescope $\Pi (\Delta_1')$.

As one would expect, this process must be carried from the left to the
right, as equations might simplify further down the line. However,
there is a subtlety in that, when discovering a simplification, one
must also rename the previously discovered constraints, as they might
mention the simplified term.

\pierre{We are simplifying references here but we should do more. We
are making a (syntactic) distinction which is finer than what the
theory (semantically) describes. There is something in the pipe but I
don't understand it in the general case. Finishing that work will
consist in extending |matchRef| (defined later) with the relevant
cases.}

This concludes our overview. Now, we have to implement the last
proposal. That's not for the faint of heart.


\subsubsection{Finding parametric hypotheses}

We have the internal context $\Delta$ lying around. We also have
access to the type of the eliminator, that is the type of the motive
and the methods. Therefore, we can already split $\Delta$ into its
parametric and non-parametric parts, $\Delta_0$ and $\Delta_1$. As we
are not interested in $\Delta_0$, we fearlessly throw it away.

We aim to implement the |findNonParametricHyps| command, which takes the context
$\Delta$ as a list of references with their types in term form and the type of
the eliminator, and returns the filtered context $\Delta_1$. The initial
dependencies are those of the motive and methods. 

> findNonParametricHyps :: Bwd (REF :<: INTM) -> TY
>     -> ProofState (Bwd (REF :<: INTM), Bwd (REF :<: INTM))
> findNonParametricHyps delta elimTy = do
>     argTypes <- unfoldTelescope elimTy
>     let deps = foldMap collectRefs argTypes
>     removeDependencies delta deps

\begin{danger}
Note that we have been careful in asking for |elimTy| here, the type
of the eliminator. One might have thought of getting the type of the
motive and methods during |introElim|, and using those.
That would not work: the motive
is defined under the scope of $\Delta$, so its lambda-lifted form includes
$\Delta$. Hence, the type of the methods are defined in terms of the
motive. Hence, all $\Delta$ is innocently included into these types,
making them useless. 
\end{danger}

The real solution is to go back to the type of the eliminator. We
unfold it with fresh references. Doing so, we are ensured that there
is no pollution, and we get what we asked for.

> unfoldTelescope :: TY -> ProofState [INTM]
> unfoldTelescope (PI _S _T) = do
>   _Stm <- bquoteHere _S
>   freshRef ("unfoldTelescope" :<: _S) $ \s -> do
>       t <- unfoldTelescope (_T $$ (A $ pval s))
>       return $ _Stm : t
> unfoldTelescope _ = return []

The dependencies can be extracted from terms in |INTM| form using the following
helper function:

> collectRefs :: INTM -> [REF]
> collectRefs = foldMap (\x -> [x])

Now, we are left with implementing |removeDependencies|.
In the case where $r \in \Delta$ belongs to the dependency set,
we exclude it from $\Delta_1$. We add the references in the
type of $r$ to the dependency set, then continue.
If $r$ is not in the dependency set, we continue and add $r$ to $\Delta_1$.

> removeDependencies :: Bwd (REF :<: INTM) -> [REF]
>     -> ProofState (Bwd (REF :<: INTM), Bwd (REF :<: INTM))
> removeDependencies (rs :< (r :<: rTy)) deps
>   | r `elem` deps  = do
>       (delta0, delta1) <- removeDependencies rs (deps `union` collectRefs rTy)
>       return (delta0 :< (r :<: rTy), delta1)
>   | otherwise      = do
>       (delta0, delta1) <- removeDependencies rs deps
>       return (delta0, delta1 :< (r :<: rTy))
> removeDependencies B0 deps = return (B0, B0)



\subsubsection{Finding removable hypotheses}

We need to do something like this to find removable hypotheses (those about
which we gain no information and hence might as well not abstract over).
However, the problem is more complex than just dependency analysis,
because of labelled types. The |shouldKeep| function doesn't work properly and
should be replaced with a proper type-directed traversal for this to make sense.

> findNonRemovableHyps :: Bwd (REF :<: INTM) -> INTM -> Bwd INTM -> Bwd (REF :<: INTM)
> findNonRemovableHyps delta goal targets = help delta []
>   where
>     deps :: [REF]
>     deps = collectRefs goal ++ foldMap collectRefs targets

>     help :: Bwd (REF :<: INTM) -> [REF :<: INTM] -> Bwd (REF :<: INTM)
>     help B0 xs = bwdList xs
>     help (delta :< (r :<: ty)) xs = help delta
>         (if (r `elem` deps) || shouldKeep ty
>             then (r :<: ty) : xs else xs)

>     shouldKeep :: Tm {d, TT} REF -> Bool
>     shouldKeep (LABEL _ _) = True
>     shouldKeep (C c) = Data.Foldable.any shouldKeep c
>     shouldKeep (L (_ :. t)) = shouldKeep t
>     shouldKeep (L (H _ _ t)) = shouldKeep t
>     shouldKeep (L (K t)) = shouldKeep t
>     shouldKeep (N t) = shouldKeep t
>     shouldKeep (t :? _) = shouldKeep t
>     shouldKeep (t :$ A u) = shouldKeep t || shouldKeep u
>     shouldKeep (_ :@ ts) = Data.Foldable.any shouldKeep ts
>     shouldKeep _ = False


\subsubsection{Representing the context as |Binder|s}

As we have seen, simplifying the motive will involve considering the 
non-parametric context $\Delta_1$ and, as we go along, remove some of its
components. We will work with $\Delta_1$ in the following form.
A |Binder| is a reference with the |INTM| representation of its type, 
and a corresponding argument term that will be used when applying the motive. 

> type Binder = (REF :<: INTM, INTM)

Note that binders are |DECL| references which are copied from the original
context and modified. This is not really a problem: remember that they are
an imitative fiction. Once we have found which binders we keep, we will
discharge them over the goal type to produce the motive.

We can get a |Binder| from a typed reference by taking the reference itself as
the second component:

> toBinder :: (REF :<: INTM) -> Binder
> toBinder (r :<: t) = (r :<: t, NP r)


\subsubsection{Extracting an element of $\Delta_1$}

Recall that, during simplification, we need to identify references
belonging to the context $\Delta_1$ and remove the
corresponding $\Pi$ in the simplified context $\Delta_1'$. However, in
|ProofState|, we cannot really remove a $\Pi$ once it has been
made. Therefore, we delay the making of the $\Pi$s until we precisely
know which ones are needed. Meanwhile, to carry out our analysis, we
directly manipulate the binders computed from $\Delta_1$.

To symbolically remove a $\Pi$, we remove the corresponding
|Binder|. When simplification ends, we simply introduce the $\Pi$s
corresponding to the remaining binders.

Let us implement the ``search and symbolic removal'' operation |lookupBinders|:
we are given a reference, which may or may not belong to the binders.
If the reference belongs to the binders, we return the binders before it,
and the binders after it (which might depend on it); if not, we return
|Nothing|.

> lookupBinders :: REF -> Bwd Binder -> Maybe (Bwd Binder, Fwd Binder)
> lookupBinders p binders = help binders F0
>   where
>     help :: Bwd Binder -> Fwd Binder -> Maybe (Bwd Binder, Fwd Binder)
>     help (binders :< b@(y :<: _, _)) zs
>         | p == y     = Just (binders, zs)
>         | otherwise  = help binders (b :> zs)
>     help B0 _        = Nothing


\subsubsection{Renaming references}

As we have seen, we will need to carry a fair amount of renaming. A renaming
operation consists in replacing some references by some other references, in a
term in |INTM| form. In such a case, renaming is simply a matter of
|fmap| over the term.

> renameTM :: [(REF, REF)] -> INTM -> INTM
> renameTM us = fmap (\ r -> maybe r id (lookup r us))


When renaming a forwards list of binders, we need to update the types of the
corresponding references and update those references in later binders.
Note that we never update the argument term (the second component of the binder)
as it needs to remain in the scope of the original context. 

> renameBinders :: [(REF, REF)] -> Bwd Binder -> Fwd Binder
>     -> (Bwd Binder, [(REF, REF)])
> renameBinders us bs ((y'@(n := DECL :<: _) :<: yt', a) :> xs) = do
>     let  yt''   = renameTM us yt'
>          y''    = n := DECL :<: evTm yt''
>          us'    = (y' , y'') : us
>     renameBinders us' (bs :< (y'' :<: yt'', a)) xs
> renameBinders us bs F0 = (bs, us) 


\subsubsection{Representing equational constraints}

Let us sum-up where we are in the construction of the motive. We are
sitting in some internal context $\Delta$. We have segregated this
context in two parts, keeping only $\Delta_1$, the non-parametric
hypotheses. Moreover, we have turned $\Delta_1$ into a list of binders. Our
mission here is to add a bunch of equational constraints to the binders,
simplifying them wherever possible. 

A |Constraint| represents an equation between a reference (in the indices $\Xi$)
with its type, and a target in $\vec{t}$ with its type.

> type Constraint =  (REF :<: INTM, (INTM :~>: INTM) :<: (INTM :~>: INTM))

We will be renaming references when we solve constraints, but we need to keep
track of the original terms (without renaming) for use when constructing
arguments to the eliminator (the second component of the binders, which are in
the scope of the original context). We use the type |a :~>: b| for a pair
in which |a| is not updated and |b| is updated. 

> data a :~>: b = a :~>: b
>   deriving (Eq, Show)

Note that there is no need to rename the left-hand sides of constraints, since they
are fresh references that do not depend on the binders. Hence we can implement
|renameConstraints| to apply a list of updates to the right-hand sides  

> renameConstraints :: [(REF, REF)] -> Bwd Constraint -> Fwd Constraint
>     -> Bwd Constraint
> renameConstraints us bs ((yyt, (s :~>: s') :<: (st :~>: st')) :> xs) = do
>     let  s''   = renameTM us s'
>          st''  = renameTM us st'
>     renameConstraints us (bs :< (yyt, (s :~>: s'') :<: (st :~>: st''))) xs
> renameConstraints us bs F0 = bs


\subsubsection{Acquiring constraints}

The |introMotive| command starts with two copies of the motive type and a list of
targets. It must be called inside the goal for the motive. It unfolds the types in
parallel, introducing fresh |lambdaParam|s on the left and working through the
targets on the right; as it does so, it accumulates constraints between the
introduced references (in $\Xi$) and the targets. It also returns the number of
extra definitions created when simplifying the motive (e.g. splitting sigmas).

> introMotive :: TY -> TY -> [INTM] -> Bwd Constraint -> Int
>     -> ProofState (Bwd Constraint, Int)

< introMotive (PI (PRF p) t) (x : xs) xs = introMotive (t $$ A (evTm x)) xs cs

If the index and target are both pairs, and the target is not a variable, then we
simplify the introduced constraints by splitting the pair. We make a new subgoal
by currying the motive type, solve the current motive with the curried version,
then continue with the target replaced by its projections.
We exclude the case where the target is a variable, because if so we might be able
to simplify its constraint.   

> introMotive (PI (SIGMA dFresh rFresh) tFresh) (PI (SIGMA dTarg rTarg) tTarg) (x:xs) cs n
>   | not . isVar $ evTm x = do
>     let mtFresh  = currySigma dFresh rFresh tFresh
>     let mtTarg   = currySigma dTarg rTarg tTarg
>     mtFresh' <- bquoteHere mtFresh

>     b :=>: _  <- make ("sig" :<: mtFresh')
>     ref       <- lambdaParam (fortran tFresh)
>     give (N (b :$ A (N (P ref :$ Fst)) :$ A (N (P ref :$ Snd))))
>     goIn

>     sTarg' <- bquoteHere (SIGMA dTarg rTarg)

>     introMotive mtFresh mtTarg ((N (x ?? sTarg' :$ Fst)) : (N (x ?? sTarg' :$ Snd)) : xs) cs (n + 1)
>   where
>     isVar :: VAL -> Bool
>     isVar (NP x)  = True
>     isVar _       = False

> introMotive (PI sFresh tFresh) (PI sTarg tTarg) (x:xs) cs n = do
>     ref      <- lambdaParam (fortran tFresh)
>     sFresh'  <- bquoteHere sFresh
>     sTarg'   <- bquoteHere sTarg
>     let c = (ref :<: sFresh', (x :~>: x) :<: (sTarg' :~>: sTarg'))
>     elimTrace $ "CONSTRAINT: " ++ show c
>     introMotive (tFresh $$ A (NP ref)) (tTarg $$ A (evTm x)) xs (cs :< c) n

> introMotive SET SET [] cs n = return (cs, n)


If |PI (SIGMA d r) t| is the type of functions whose domain is a sigma-type, then
|currySigma d r t| is the curried function type that takes the projections
separately. 

> currySigma :: VAL -> VAL -> VAL -> VAL
> currySigma d r t = PI d . L $ (fortran r) :. [.a. 
>               PI (r -$ [NV a]) . L $ (fortran t) :. [.b. 
>               t -$ [PAIR (NV a) (NV b)]]]


\subsubsection{Simplifying constraints}

The |simplifyMotive| command takes a list of binders, a list of constraints and
a goal type. It computes an updated list of binders and an updated goal type.

To the left, we have a backwards list of binders: updated references and types,
and non-updated argument terms.

To the right, we have a forwards list of constraints: references in $\Xi$ together
with the term representation of their type, and typed terms in $\Delta$ to which
the references are equated.

> simplifyMotive :: Bwd Binder -> Fwd Constraint -> INTM
>     -> ProofState (Bwd Binder, INTM)

For each constraint, we check if the term on the right is a reference. If so,
we check the equation is homogeneous (so substitution is allowed) and look for the
reference in $\Delta$. If we find it, we can simplify by removing the equation,
updating the binder and renaming the following binders, constraints and term. 

> simplifyMotive bs (c@(x :<: xt, (q :~>: q') :<: (pt :~>: pt')) :> cs) tm
>   | NP p' <- evTm q' = do
>     eq <- withNSupply $ equal $ SET :>: (pty x, pty p')
>     case (eq, lookupBinders p' bs) of
>         (True, Just (pre, post)) -> do
>             let  (post', us)  = renameBinders [(p', x)] B0 post
>                  cs'          = renameConstraints us B0 cs
>                  tm'          = renameTM us tm
>             simplifyMotive (pre <+> post') (cs' <>> F0) tm'

If the conditions do not hold, we simply have to go past the constraint by turning
it into a binder:

>         _ -> passConstraint bs c cs tm

> simplifyMotive bs (c :> cs) tm = passConstraint bs c cs tm

Eventually, we run out of constraints, and we win:

> simplifyMotive bs F0 tm = return (bs, tm)


To pass a constraint, we append a binder with a fresh reference whose type is the
proof of the equation. When applying the motive, we will need to use reflexivity 
applied to the non-updated target.

> passConstraint :: Bwd Binder -> Constraint -> Fwd Constraint -> INTM
>     -> ProofState (Bwd Binder, INTM)
> passConstraint bs (x :<: xt, (s :~>: s') :<: (st :~>: st')) cs tm = do
>     let qt = PRF (EQBLUE (xt :>: NP x) (st' :>: s'))
>     elimTrace $ "PASS: " ++ show qt
>     freshRef ("qsm" :<: evTm qt)
>         (\ q -> simplifyMotive
>             (bs :< (q :<: qt, N (P refl :$ A st :$ A s))) cs tm)


\subsubsection{Building the motive}

Finally, we can make the motive, hence closing the subgoal. This
simply consists in chaining the commands above, and give the computed
term. Unless we've screwed things up, |giveOutBelow| should always be happy.

> makeMotive ::  TY -> INTM -> Bwd (REF :<: INTM) -> Bwd INTM -> TY ->
>                ProofState (Bwd (REF :<: INTM), [Binder])
> makeMotive motiveType goal delta targets elimTy = do
>     elimTrace $ "goal: " ++ show goal
>     elimTrace $ "targets: " ++ show targets

Extract non-parametric, non-removable hypotheses $\Delta_1$ from the context $\Delta$:

>     elimTrace $ "delta: " ++ show (fmap (\ ((n := _) :<: _) -> n) delta)
>     (delta0, delta1) <- findNonParametricHyps delta elimTy
>     elimTrace $ "delta1: " ++ show (fmap (\ ((n := _) :<: _) -> n) delta1)

Transform $\Delta_1$ into Binder form:

>     let binders = fmap toBinder delta1

Introduce $\Xi$ and generate constraints between its references and the targets:

>     (constraints, n) <- introMotive motiveType motiveType (trail targets) B0 0
>     elimTrace $ "constraints: " ++ show constraints

Simplify the constraints to produce an updated list of binders and goal type:

>     (binders', goal') <- simplifyMotive binders (constraints <>> F0) goal
>     elimTrace $ "binders': " ++ show binders'
>     elimTrace $ "goal': " ++ show goal'

Discharge the binders over the goal type to produce the motive:

>     let goal'' = liftType' (fmap fst binders') goal'
>     elimTrace $ "goal'': " ++ show goal''
>     giveOutBelow goal''

Return to the construction of the rebuilt eliminator, by going out the same number
of times as |introMotive| went in:

>     replicateM_ n goOut
>     return (delta0, trail binders')


\subsection{Putting things together}

Now we can combine the pieces to produce the |elim| command: 

> elim :: Maybe REF -> (TY :>: EXTM) -> ProofState [EXTM :=>: VAL]
> elim comma (elimTy :>: elim) = do 

Here we go. First, we need to retrieve some information about our
goal and its context, before we start modifying the development.

>     (goal :=>: _) <- getGoal "T"
>     delta <- getLocalContext comma

We call |introElim| to rebuild the eliminator as a definition, check that
everything is correct, and make subgoals for the motive and methods. 

>     (elimName, motiveType, targets) <- introElim (elimTy :>: elim)

Then we call |makeMotive| to introduce the indices, build and simplify
constraints, and solve the motive subgoal. 

>     (delta0, binders) <- makeMotive motiveType goal delta targets elimTy

We leave the definition of the rebuilt eliminator, with the methods
unimplemented, and return to the original problem.

>     goOut

We solve the problem by applying the eliminator. 
Since the binders already contain the information we need in their second
components, it is straightforward to build the term we want and to give it.
Note that we have to look up the latest version of the rebuilt eliminator
because its definition will have been updated when the motive was defined.

>     Just (elim :=>: _) <- lookupName elimName
>     tt <- give $ N $ elim $## map snd binders

Now we have to move the methods. We use the usual trick: make new definitions
and solve the old goals with the new ones. First we collect the types of the
methods, quoting them (to expand the definition of the motive) and lifting them
over $\Delta_0$:

>     toMotive
>     methodTypes <- many $ do
>         goDown
>         _ :=>: ty <- getHoleGoal
>         ty' <- bquoteHere ty
>         return (liftType' delta0 ty')

Next we move to the top of the original development, and make the lifted methods:

>     goOut  -- to makeE
>     goOut  -- to the original goal
>     cursorTop
>     liftedMethods <- traverse (make . ("lm" :<:)) methodTypes

Then we return to the methods and solve them with the lifted versions:

>     cursorBottom
>     toMotive
>     let args = fmap (NP . fstEx) delta0
>     flip traverse liftedMethods $ \ tt -> do
>         goDown
>         give $ N $ termOf tt $## args
>      

Finally we move back to the bottom of the original development:   

>     goOut
>     goOut
>     return liftedMethods

> toMotive :: ProofState ()
> toMotive = goIn >> goIn >> goTop


This leaves us on the same goal we started with. For interactive use, we will
typically want to move to the first (lifted) method:

> toFirstMethod :: ProofState ()
> toFirstMethod = goIn >> goTop

The |getLocalContext| command takes a comma and returns the local
context, by looking up the parameters above and dropping those before
the comma, if one is supplied.  Regardless of the comma, we only go
back as far as a |CurrentEntry| with name |magicImplName| if one
exists, so shared parameters for programming problems will always be
excluded.

> getLocalContext :: Maybe REF -> ProofState (Bwd (REF :<: INTM))
> getLocalContext comma = do
>     delta <- getDefinitionsToImpl
>     return . bwdList $ case comma of 
>         Nothing  -> delta
>         Just c   -> dropWhile (\ (r :<: _) -> c /= r) delta




We make elimination accessible to the user by adding it as a Cochon tactic:

> import -> CochonTacticsCode where
>   elimCTactic :: Maybe RelName -> DExTmRN -> ProofState String
>   elimCTactic c r = do 
>     c' <- traverse resolveDiscard c
>     (e :=>: _ :<: elimTy) <- elabInferFully r
>     elim c' (elimTy :>: e)
>     toFirstMethod
>     return "Eliminated. Subgoals awaiting work..."

> import -> CochonTactics where
>   : (simpleCT
>     "eliminate"
>     (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
>                                               |id tokenAscription |)|)
>     (\[n,e] -> elimCTactic (argOption (unDP . argToEx) n) (argToEx e))
>     "eliminate [<comma>] <eliminator> - eliminates with a motive.")
