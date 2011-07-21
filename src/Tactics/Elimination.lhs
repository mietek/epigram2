\section{Elimination with a Motive}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternGuards #-}

> module Tactics.Elimination where

> import Prelude hiding (elem, exp)

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (any,find)
> import Data.List hiding (elem)
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.NatFinVec
> import Kit.Trace

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.ProofContext
> import ProofState.Structure
> import ProofState.GetSet
> import ProofState.Navigation
> import ProofState.Interface

> import Tactics.Unification

> import DisplayLang.Name

> import Debug.Trace

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



\subsubsection{Finding parametric hypotheses}

We have the internal context $\Delta$ lying around. We also have
access to the type of the eliminator, that is the type of the motive
and the methods. Therefore, we can already split $\Delta$ into its
parametric and non-parametric parts, $\Delta_0$ and $\Delta_1$. As we
are not interested in $\Delta_0$, we fearlessly throw it away.

> splitDelta :: Int -> Bwd (Int, String, TY) -> [EXP] -> 
>               (Bwd (Int, String, TY), Bwd (Int, String, TY))
> splitDelta lev B0 _ = (B0, B0)
> splitDelta lev (bs :< b@(l,s,t)) es | any (\e -> occurs lev Nothing [l] (SET :>: e)) es = let (delta0, delta1) = splitDelta lev bs (t:es) in (delta0 :< b,delta1)
> splitDelta lev (bs :< b) es = 
>   let (delta0, delta1) = splitDelta lev bs es in (delta0, delta1 :< b)


> unfoldTelescope :: Int -> VAL -> Bwd (Int,String,TY) -> (Int,Bwd (Int, String,TY), VAL)
> unfoldTelescope lev (PI _S _T) es = let x = fortran "s" [ev _T] undefined in
>    unfoldTelescope (lev+1) (ev _T $$. (P (lev,"s",_S) :$ B0)) (es :< (lev,x,_S))
> unfoldTelescope lev _T es = (lev, es, _T) 

> {-

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

> -}


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

> lookupBinders :: (Int, String, TY) -> Bwd (Int, String, TY) -> Maybe (Bwd (Int, String, TY), Fwd (Int, String, TY))
> lookupBinders (l,s,t) binders = help binders F0
>   where
>     help :: Bwd (Int, String, TY) -> Fwd (Int, String, TY) -> Maybe (Bwd (Int, String, TY), Fwd (Int, String, TY))
>     help (binders :< b@(l',s',t')) zs
>         | l == l'     = Just (binders, zs)
>         | otherwise  = help binders (b :> zs)
>     help B0 _        = Nothing




\subsubsection{Representing equational constraints}

Let us sum-up where we are in the construction of the motive. We are
sitting in some internal context $\Delta$. We have segregated this
context in two parts, keeping only $\Delta_1$, the non-parametric
hypotheses. Moreover, we have turned $\Delta_1$ into a list of binders. Our
mission here is to add a bunch of equational constraints to the binders,
simplifying them wherever possible. 

A |Constraint| represents an equation between a reference (in the indices $\Xi$)
with its type, and a target in $\vec{t}$ with its type.

> type Constraint =  ((EXP :<: TY) :~: (EXP :<: TY), (EXP :<: TY))

We will be renaming references when we solve constraints, but we need to keep
track of the original terms (without renaming) for use when constructing
arguments to the eliminator (the second component of the binders, which are in
the scope of the original context). 

> data a :~: b = a :~: b
>   deriving (Eq, Show)

> {-

\subsubsection{Acquiring constraints}

The |introMotive| command starts with two copies of the motive type and a list of
targets. It must be called inside the goal for the motive. It unfolds the types in
parallel, introducing fresh |lambdaParam|s on the left and working through the
targets on the right; as it does so, it accumulates constraints between the
introduced references (in $\Xi$) and the targets. It also returns the number of
extra definitions created when simplifying the motive (e.g. splitting sigmas).

> introMotive :: VAL -> VAL -> [EXP] -> Bwd Constraint -> Int
>     -> ProofState (Bwd Constraint, Int)


If the index and target are both pairs, and the target is not a variable, then we
simplify the introduced constraints by splitting the pair. We make a new subgoal
by currying the motive type, solve the current motive with the curried version,
then continue with the target replaced by its projections.
We exclude the case where the target is a variable, because if so we might be able
to simplify its constraint.   

> introMotive (PI (SIGMA dFresh rFresh) tFresh) (PI (SIGMA dTarg rTarg) tTarg) (x:xs) cs n
>   | not . isVar $ ev x = do
>     let mtFresh  = currySigma dFresh rFresh tFresh
>     let mtTarg   = currySigma dTarg rTarg tTarg

>     b  <- make ("sig" :<: mtFresh)
>     ref       <- lambdaParam (fortran "s" [ev tFresh] undefined)
>     give (b $$. (apply {Exp} (toBody ref) Hd) $$. (apply {Exp} (toBody ref) Tl))
>     goIn

>     introMotive (ev mtFresh) (ev mtTarg) ((x $$ Hd) : (x $$ Tl) : xs) cs (n + 1)
>   where
>     isVar :: VAL -> Bool
>     isVar (P x :$ B0)  = True
>     isVar _            = False

> introMotive (PI sFresh tFresh) (PI sTarg tTarg) (x:xs) cs n = do
>     ref@(P r)  <- lambdaParam (fortran "s" [ev tFresh] undefined)
>                      :: ProofState (Tm {Head, Exp, Z})
>     let c = (r, (x :~: x) :<: (sTarg :~: sTarg))
>     elimTrace $ "CONSTRAINT: " ++ show c
>     introMotive (ev tFresh $$. toBody ref) (ev tTarg $$. x) xs (cs :< c) n

> introMotive SET SET [] cs n = return (cs, n)

> -}

If |PI (SIGMA d r) t| is the type of functions whose domain is a sigma-type, then
|currySigma d r t| is the curried function type that takes the projections
separately. 

> currySigma :: EXP -> EXP -> EXP -> EXP
> currySigma d r t = ((fortran "a" [ev r] undefined, d) ->>  \a -> 
>                    ((fortran "b" [ev t] undefined, wr r a) ->>  \b -> 
>                    wr t (PAIR a b)))


> {-

\subsubsection{Simplifying constraints}

The |simplifyMotive| command takes a list of binders, a list of constraints and
a goal type. It computes an updated list of binders and an updated goal type.

To the left, we have a backwards list of binders: updated references and types,
and non-updated argument terms.

To the right, we have a forwards list of constraints: references in $\Xi$ together
with the term representation of their type, and typed terms in $\Delta$ to which
the references are equated.

> simplifyMotive :: Int -> Bwd Binder -> Fwd Constraint -> EXP
>     -> ProofState (Bwd Binder, EXP)

For each constraint, we check if the term on the right is a reference. If so,
we check the equation is homogeneous (so substitution is allowed) and look for the
reference in $\Delta$. If we find it, we can simplify by removing the equation,
updating the binder and renaming the following binders, constraints and term. 

> simplifyMotive lev bs (c@(x@(l, s, t), (q :~: q') :<: (pt :~: pt')) :> cs) tm
>   | P p'@(l', s', t') :$ B0 <- ev q' = do
>     eq <- getDevLev >>= \l -> (| (equal l $ SET :>: (t, t')) |)
>     case (eq, lookupBinders p' bs) of
>         (True, Just (pre, post)) -> do
>             let  (post', us)  = renameBinders [(p', x)] B0 post
>                  cs'          = renameConstraints us B0 cs
>                  tm'          = renameTM us tm
>             simplifyMotive lev (pre <+> post') (cs' <>> F0) tm'

If the conditions do not hold, we simply have to go past the constraint by turning
it into a binder:

>         _ -> passConstraint lev bs c cs tm

> simplifyMotive lev bs (c :> cs) tm = passConstraint lev bs c cs tm

Eventually, we run out of constraints, and we win:

> simplifyMotive lev bs F0 tm = return (bs, tm)


To pass a constraint, we append a binder with a fresh reference whose type is the
proof of the equation. When applying the motive, we will need to use reflexivity 
applied to the non-updated target.

> passConstraint :: Int -> Bwd Binder -> Constraint -> Fwd Constraint -> EXP
>     -> ProofState (Bwd Binder, EXP)
> passConstraint l bs (x@(_,_,xt), (s :~: s') :<: (st :~: st')) cs tm = do
>     let qt = PRF (EQ xt (P x :$ B0) st' s')
>     elimTrace $ "PASS: " ++ show qt
>     simplifyMotive (l+1)
>             (bs :< ((l, "qsm", qt), Refl st s :$ B0)) cs tm


\subsubsection{Building the motive}

Finally, we can make the motive, hence closing the subgoal. This
simply consists in chaining the commands above, and give the computed
term. Unless we've screwed things up, |giveOutBelow| should always be happy.

> makeMotive ::  TY -> EXP -> Bwd (Int, String, TY) -> Bwd EXP -> TY ->
>                ProofState (Bwd (Int, String, TY), Bwd Binder)

> makeMotive motiveType goal delta targets elimTy = do
>     elimTrace $ "goal: " ++ show goal
>     elimTrace $ "targets: " ++ show targets

Extract non-parametric, non-removable hypotheses $\Delta_1$ from the context $\Delta$:

>     elimTrace $ "delta: " ++ show delta
>     lev <- getDevLev
>     (lev', unf) <- unfoldTelescope lev (ev elimTy)
>     elimTrace $ "tel: " ++ show unf
>     let (delta0, delta1) = (splitDelta lev' delta unf)

>     elimTrace $ "delta1: " ++ show delta1

Transform $\Delta_1$ into Binder form:

>     let binders = fmap toBinder delta1

Introduce $\Xi$ and generate constraints between its references and the targets:


>     (constraints, n) <- introMotive (ev motiveType) (ev motiveType) (trail targets) B0 0
>     elimTrace $ "constraints: " ++ show constraints

Simplify the constraints to produce an updated list of binders and goal type:

>     lev <- getDevLev
>     (binders', goal') <- simplifyMotive lev binders (constraints <>> F0) goal
>     elimTrace $ "binders': " ++ show binders'
>     elimTrace $ "goal': " ++ show goal'

Discharge the binders over the goal type to produce the motive:

>     let goal'' = bwdVec (fmap fst binders') 
>                    (\n ys -> piLift {n} ys goal')
>     elimTrace $ "goal'': " ++ show goal''
>     giveOutBelow goal''

Return to the construction of the rebuilt eliminator, by going out the same number
of times as |introMotive| went in:

>     replicateM_ n goOut
>     return (delta0, binders')

> -}

\subsection{Putting things together}

Now we can combine the pieces to produce the |elim| command: 

> intros :: [ (Int, String, TY) ] -> LEnv {Z} -> ProofState (LEnv {Z})
> intros [] lenv = (| lenv |)
> intros ((l, s, t) : ds) lenv = do
>   h <- assumeParam (s :<: ((lenv, INil) <:/> t))
>   intros ds ((l, toBody h) : lenv)

> pintros :: [ (Int, String, TY) ] -> LEnv {Z} -> ProofState (LEnv {Z})
> pintros [] lenv = (| lenv |)
> pintros ((l, s, t) : ds) lenv = do
>   h <- piParam (s :<: ((lenv, INil) <:/> t))
>   pintros ds ((l, toBody h) : lenv)


> buildConstraints :: Int -> VAL -> VAL -> [Elim EXP] -> Bwd Constraint -> Bwd (Int, String, TY) -> (Int, Bwd Constraint, Bwd (Int, String, TY))
> buildConstraints lev (PI sFresh tFresh) (PI sTarg tTarg) (A x:xs) cs ps = 
>     let p = (lev, fortran "s" [ev tFresh] undefined, sFresh)
>         r = P p :$ B0
>         c = ((r :<: sFresh) :~: (x :<: sTarg), (x :<: sTarg))
>     in buildConstraints (lev + 1) (ev tFresh $$. r) (ev tTarg $$. x) xs (cs :< c) (ps :< p)

> buildConstraints lev SET SET [] cs ps = (lev, cs, ps)

> isPSpine :: VAL -> Maybe ((Int, String, TY), Bwd (Elim EXP))
> isPSpine (P x :$ as)  = Just (x, as)
> isPSpine _            = Nothing

> constraintsToEqns :: Int -> [Constraint] -> [(Int, String, TY)]
> constraintsToEqns lev [] = []
> constraintsToEqns lev (((x :<: xty) :~: (t :<: tty), r :<: rty):cs) =
>     (lev, "q", PRF (EQ xty x tty t)) : constraintsToEqns (lev+1) cs

> createMethods :: Bwd (Elim EXP) -> LEnv {Z} -> [(Int, String, TY)] -> EXP -> ProofState EXP
> createMethods d0 lenv []           tm = return tm
> createMethods d0 lenv ((l,s,t):ms) tm = do
>     (df, r) <- make' (s :<: exp (evalEager {Val} ENil ((lenv, INil) <:/> t :: EXP)) )
>     createMethods d0 ((l, r):lenv) ms (tm $$. (def df $$$ d0))


> simplifyConstraints :: Int -> Bwd (Int, String, TY) -> (Bwd Constraint, Fwd Constraint) -> EXP ->
>                            (Bwd (Int, String, TY), Bwd Constraint, EXP)
> simplifyConstraints lev delta1 (bs, F0) e = (delta1, bs, e)
> simplifyConstraints lev delta1 (bs, c@((x :<: xty) :~: (t :<: tty), r :<: rty):>fs) e =
>     case (evv x, evv xty, evv t, evv tty, evv rty) of
>         (_, PRF _, _, _, _)  -> simplifyConstraints lev delta1 (bs, fs) e
>         (_, _, _, PRF _, _)  -> simplifyConstraints lev delta1 (bs, fs) e
>         (x, xty, P p@(pl, _, _) :$ B0, tty, _) | bwdNull bs || equal lev (SET :>: (exp xty, exp tty)),
>                                    Just (ls, rs) <- lookupBinders p delta1
>                -> let 
>                       ptox :: EXP -> EXP
>                       ptox  = (([(pl, exp x)], INil) <:/>)
>                       rs'   = fmap (\ (l, s, t) -> (l, s, ptox t)) rs
>                       bs'   = fmap (\ (y :~: (t :<: tty), r) -> (y :~: (ptox t :<: ptox tty), r)) bs
>                       fs'   = fmap (\ (y :~: (t :<: tty), r) -> (y :~: (ptox t :<: ptox tty), r)) fs
>                   in simplifyConstraints lev (ls <>< rs') (bs', fs') (ptox e)
>         (x, SIGMA _X0 _X1, PAIR th tt, SIGMA _T0 _T1, SIGMA _R0 _R1) ->
>             simplifyConstraints lev delta1
>                 (bs, ((exp (x $$ Hd) :<: _X0) :~: (th :<: _T0), (exp (ev r $$ Hd) :<: _R0))
>                      :> ((exp (x $$ Tl) :<: _X1 $$. (x $$ Hd)) :~: (tt :<: _T1 $$. th),
>                                   (exp (ev r $$ Tl) :<: exp (ev _R1 $$. (ev r $$ Hd)))) :> fs) e
>         _ -> simplifyConstraints lev delta1 (bs :< c, fs) e


> elim :: (TY :>: EXP) -> ProofState [Name]

> elim (elimTy :>: elim) = do 

Here we go. First, we need to retrieve some information about our
goal and its context, before we start modifying the development.

>     goal <- getGoal "EWAM"
>     delta <- (| paramsBwd getInScope |)
>     lev <- getDevLev
>     let (lev',unf',_Pt) = unfoldTelescope lev (ev elimTy) B0
>     let unf@((_Pl,_,_PTy):methodTypes) = trail unf'
>     ts <- case isPSpine _Pt of
>             Just ((_Pl',_,_), ts) | _Pl == _Pl' -> (elimTrace $ "PTY: " ++ show _Pt ++ " Pl: " ++ show _Pl) >> return ts
>             _ -> throwError' $ err "Elim targetting wrong"  
>     let (delta0, delta1) = splitDelta lev' delta (fmap (\(_,_,ty) -> ty) $ trail unf)
>     elimTrace $ "Delta0: " ++ show delta0
>     let evPTy = ev _PTy
>     let (lev'', cs, xi) = buildConstraints lev evPTy evPTy (trail ts) B0 B0 
>     elimTrace $ "Constraints: " ++ show cs
>     elimTrace $ "Xi: " ++ show xi

>     (delta1, cs, goal) <- return $ simplifyConstraints lev'' delta1 (B0, cs <>> F0) goal

>     makeModule' NixHyps "elim" >> goIn
>     lenvDelta0 <- intros (trail delta0) []
>     makeModule "Motive"
>     goIn
>     lenv <- intros (trail xi) lenvDelta0

>     moduleToGoal SET
>     lenv <- pintros (trail delta1) lenv            

>     let eek = constraintsToEqns lev'' (trail cs)
>     elimTrace $ "eek: " ++ show eek
>     elimTrace $ "lenv: " ++ show lenv
>     lenv <- pintros eek lenv

>     motiveDef <- giveOutBelow ((lenv, INil) <:/> goal)
>     let delta0app = fmap (A . toBody . P) delta0
>     let motive = def motiveDef $$$ delta0app

>     elimTrace $ "motive: " ++ show motive

>     tm <- createMethods delta0app ((_Pl, (lenvDelta0, INil) <:/> motive) : lenvDelta0) methodTypes (elim $$. motive)
>     let tm'   = tm $$$ fmap (A . toBody . P) delta1
>         tm''  = tm' $$$ fmap (\ (_, (r :<: rty)) -> A (toBody (Refl rty r))) cs
>     elimTrace $ "TM'': " ++ show tm''

>     goOut
>     give tm''

> {-

We call |introElim| to rebuild the eliminator as a definition, check that
everything is correct, and make subgoals for the motive and methods. 

>     (elimD, motiveType, targets) <- introElim (ev elimTy :>: elim)

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

<     Just elimD' <- lookupName (defName elimD)
<     tt <- give $  elimD' $$$. fmap snd binders  

\note{We should move the methods but the code below created bogus a
proofstate, where the lifted methods had types referring to the motive which
was out of scope --- more care is needed!}

<     toMotive
<     methods <- many $ do
<       goDown
<       getCurrentName

Now we have to move the methods. We use the usual trick: make new definitions
and solve the old goals with the new ones. First we collect the types of the
methods, quoting them (to expand the definition of the motive) and lifting them
over $\Delta_0$:

<     toMotive
<     methodTypes <- many $ do
<         goDown
<         ty <- getHoleGoal
<         return $ liftType' delta0 ty

Next we move to the top of the original development, and make the lifted methods:

<     goOut  -- to makeE
<     goOut  -- to the original goal
<     cursorTop
<     liftedMethods <- traverse (make . ("lm" :<:)) methodTypes

Then we return to the methods and solve them with the lifted versions:


<     cursorBottom
<     toMotive
<     let args = fmap (\x -> P x :$ B0) delta0
<     flip traverse liftedMethods $ \ tt -> do
<         goDown
<         give $ tt $$$. args

Finally we move back to the bottom of the original development:   

<     goOut
<     goOut
<     return liftedMethods

> -}

>     return [] -- methods 


> toMotive :: ProofState ()
> toMotive = goIn >> goIn >> goTop


This leaves us on the same goal we started with. For interactive use, we will
typically want to move to the first (lifted) method:

< toFirstMethod :: ProofState ()
< toFirstMethod = goIn >> goTop

We make elimination accessible to the user by adding it as a Cochon tactic:

