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

An \emph{eliminator}\index{eliminator} is a term of type
$$\Delta \Tn e : (P : \Xi \rightarrow \Set) 
                            \rightarrow \vec{M} 
                            \rightarrow P\, \vec{t}$$
where we call $P$ the \emph{motive}\index{motive} of the elimination,
$\Xi$ the \emph{indices}, $\vec{M}$ the \emph{methods}\index{method},
$\vec{t}$ the \emph{targets}\index{target} and $P\, \vec{t}$ the
\emph{result type}. Elimination with a motive starts in the proof
state
\begin{center}
\begin{minipage}{5cm}
\begin{alltt}
[ \((\Delta)\) \(\rightarrow\)
] := ? : \(T\)
\end{alltt}
\end{minipage}
\end{center}
where $\Delta$ is the telescope of parameters in scope, and $T$ is the
goal type. It splits $\Delta$ into telescopes of \emph{parametric} and
\emph{non-parametric} hypotheses $\Delta_0$ and $\Delta_1$
(respectively). The idea is to produce the refined proof state
\begin{alltt}
[ \((\Delta)\) \(\rightarrow\)
  \(elim\) (NIX) [
    \((\Delta\sb{0})\) \(\rightarrow\)
    \(P\) [
      \((\Xi) \rightarrow\)
    ] := \(((\Delta\sb{1}) \rightarrow (\Xi = \vec{t}) \rightarrow T) : \Set\)
    \(m\sb{0}\) [] := ? : \(M\sb{0}\)
    ...
    \(m\sb{n}\) [] := ? : \(M\sb{n}\)
  ]
] := \(e (elim.P \Delta\sb{0}) (elim.m\sb{0} \Delta\sb{0}) \ldots (elim.m\sb{n} \Delta\sb{0}) \vec{t} \Delta\sb{1} (refl \vec{t}) : T\)
\end{alltt}
That is, we create a new module (called $elim$) which contains a
definition for the motive $P$ and subgoals corresponding to the
methods. We solve the original goal by applying the eliminator to the
motive and methods. Notice that, inside the module, the hypotheses in
scope are filtered to leave only the parametric hypotheses $\Delta_0$,
while the non-parametric hypotheses $\Delta_1$ will be in scope for
each goal $M_i$ since they appear in the motive.

Given an eliminator with its type, it |elim| tactic applies
elimination with a motive to the current goal and returns the names of
the subgoals produced (corresponding to the methods of the
eliminator).

< elim :: (TY :>: EXP) -> ProofState [Name]



\subsection{Finding parametric hypotheses}

Given the context $\Delta$, and a list of types, we can split $\Delta$
into its parametric and non-parametric parts, $\Delta_0$ and
$\Delta_1$. The idea (initially) is that $\Delta_0$ is the minimal
support for the types in the list. We will populate this list with the
types from unfolding the eliminator's telescope. Thus $\Delta_0$
contains the hypotheses that the motive and methods depend on, and
hence must be made parametric.

There are various other things we might want to exclude from
$\Delta_1$, depending on whether we have a recursive or non-recursive
eliminator (and hence whether we should maximise the induction
hypothesis), but for now we keep things simple (hah!). 

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


\subsection{Finding removable hypotheses}

We need to do something like this to find removable hypotheses (those about
which we gain no information and hence might as well not abstract over).
However, the problem is more complex than just dependency analysis,
because of labelled types. The |shouldKeep| function doesn't work properly and
should be replaced with a proper type-directed traversal for this to make sense.

< findNonRemovableHyps :: Bwd (REF :<: INTM) -> INTM -> Bwd INTM -> Bwd (REF :<: INTM)
< findNonRemovableHyps delta goal targets = help delta []
<   where
<     deps :: [REF]
<     deps = collectRefs goal ++ foldMap collectRefs targets

<     help :: Bwd (REF :<: INTM) -> [REF :<: INTM] -> Bwd (REF :<: INTM)
<     help B0 xs = bwdList xs
<     help (delta :< (r :<: ty)) xs = help delta
<         (if (r `elem` deps) || shouldKeep ty
<             then (r :<: ty) : xs else xs)

<     shouldKeep :: Tm {d, TT} REF -> Bool
<     shouldKeep (LABEL _ _) = True
<     shouldKeep (C c) = Data.Foldable.any shouldKeep c
<     shouldKeep (L (_ :. t)) = shouldKeep t
<     shouldKeep (L (H _ _ t)) = shouldKeep t
<     shouldKeep (L (K t)) = shouldKeep t
<     shouldKeep (N t) = shouldKeep t
<     shouldKeep (t :? _) = shouldKeep t
<     shouldKeep (t :$ A u) = shouldKeep t || shouldKeep u
<     shouldKeep (_ :@ ts) = Data.Foldable.any shouldKeep ts
<     shouldKeep _ = False



\subsection{Extracting an element of $\Delta_1$}

During simplification, we need to identify binders belonging to the
context $\Delta_1$ and remove them. Let us implement the ``search and
symbolic removal'' operation |lookupBinders|: we are given a binder,
which may or may not belong to $\Delta_1$.  If it does, we return the
binders before it, and the binders after it (which might depend on
it); if not, we return |Nothing|.

> lookupBinders :: (Int, String, TY) -> Bwd (Int, String, TY) ->
>     Maybe (Bwd (Int, String, TY), Fwd (Int, String, TY))
> lookupBinders (l,s,t) binders = help binders F0
>   where
>     help :: Bwd (Int, String, TY) -> Fwd (Int, String, TY) ->
>                 Maybe (Bwd (Int, String, TY), Fwd (Int, String, TY))
>     help (binders :< b@(l',s',t')) zs
>         | l == l'     = Just (binders, zs)
>         | otherwise  = help binders (b :> zs)
>     help B0 _        = Nothing




\subsection{Equational constraints}

Let us sum-up where we are in the construction of the motive. We are
sitting in some internal context $\Delta$. We have segregated this
context in two parts, keeping only $\Delta_1$, the non-parametric
hypotheses. Moreover, we have turned $\Delta_1$ into a list of binders. Our
mission here is to add a bunch of equational constraints to the binders,
simplifying them wherever possible. 

A |Constraint| represents an equation between a reference (in the indices $\Xi$)
with its type, and a target in $\vec{t}$ with its type.

> type Constraint = ((EXP :<: TY) :~: (EXP :<: TY), (EXP :<: TY))

We will be renaming references when we solve constraints, but we need to keep
track of the original terms (without renaming) for use when constructing
arguments to the eliminator (the second component of the binders, which are in
the scope of the original context). 

> data a :~: b = a :~: b
>   deriving (Eq, Show)


\subsubsection{Acquiring constraints}

The |buildConstraints| command starts with two copies of the motive
type and a list of targets. It unfolds the types in parallel,
introducing fresh parameters on the left (from the given base level)
and working through the targets on the right; as it does so, it
accumulates a list of constraints between the introduced levels (in
$\Xi$) and the targets. It returns the final level, a list of
constraints generated and a list of parameters introduced.

> buildConstraints :: Int -> VAL -> VAL -> [Elim EXP] ->
>                         Bwd Constraint -> Bwd (Int, String, TY) ->
>                         (Int, Bwd Constraint, Bwd (Int, String, TY))
> buildConstraints lev (PI sFresh tFresh) (PI sTarg tTarg) (A x:xs) cs ps = 
>     let p = (lev, fortran "s" [ev tFresh] undefined, sFresh)
>         r = P p :$ B0
>         c = ((r :<: sFresh) :~: (x :<: sTarg), (x :<: sTarg))
>     in buildConstraints (lev + 1) (ev tFresh $$. r) (ev tTarg $$. x) xs (cs :< c) (ps :< p)

> buildConstraints lev SET SET [] cs ps = (lev, cs, ps)




\subsubsection{Simplifying constraints}

The |simplifyConstraints| command takes a list of binders $\Delta_1$,
a list zipper of constraints and a goal type. It computes updated
lists of binders and constraints, and an updated goal type. Starting
with a forwards list of constraints, it moves them from right to left,
dropping those which are trivial (e.g. between two proofs) and
simplifying $\Delta_1$ by removing each binder that is constrained to
equal a term of the same type. Whenever a binder is removed, it must
be replaced by the target in the rest of the binders and the
constraints.

> simplifyConstraints :: Int -> Bwd (Int, String, TY) ->
>                            (Bwd Constraint, Fwd Constraint) -> EXP ->
>                                (Bwd (Int, String, TY), Bwd Constraint, EXP)
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


\subsubsection{Converting constraints to binders}

Once we have simplifed the constraints, those that remain must become
$\Pi$-binders in the motive.  The |constraintsToEqns| function
converts a list of constraints into a list of binders, numbering them
with levels starting at the given base level.

> constraintsToEqns :: Int -> [Constraint] -> [(Int, String, TY)]
> constraintsToEqns lev [] = []
> constraintsToEqns lev (((x :<: xty) :~: (t :<: tty), r :<: rty):cs) =
>     (lev, "q", PRF (EQ xty x tty t)) : constraintsToEqns (lev+1) cs



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

> isPSpine :: VAL -> Maybe ((Int, String, TY), Bwd (Elim EXP))
> isPSpine (P x :$ as)  = Just (x, as)
> isPSpine _            = Nothing

> createMethods :: Bwd (Elim EXP) -> LEnv {Z} -> [(Int, String, TY)] -> EXP -> Bwd Name -> 
>                      ProofState (EXP, Bwd Name)
> createMethods d0 lenv []           tm ns = return (tm, ns)
> createMethods d0 lenv ((l,s,t):ms) tm ns = do
>     (df, r) <- make' (s :<: exp (evalEager {Val} ENil ((lenv, INil) <:/> t :: EXP)) )
>     createMethods d0 ((l, r):lenv) ms (tm $$. (def df $$$ d0)) (ns :< defName df)



> elim :: (TY :>: EXP) -> ProofState [Name]
> elim (elimTy :>: elim) = do 

Here we go. First, we need to retrieve some information about our
goal and its context, before we start modifying the development.

>     goal   <- getGoal "EWAM"
>     delta  <- (| paramsBwd getInScope |)
>     lev    <- getDevLev

We unfold the eliminator type telescope |elimTel| to extract the level
|_Pl| and type |_PTy| of the motive, the method types (as binders) and
the application of the motive to the targets |_Pt|. Assuming the
latter is correctly formed, we can extract the targets |ts|.

>     let (lev', elimTel', _Pt) = unfoldTelescope lev (ev elimTy) B0
>     let elimTel@((_Pl,_,_PTy):methodTypes) = trail elimTel'
>     ts <- case isPSpine _Pt of
>             Just ((_Pl',_,_), ts) | _Pl == _Pl' -> return ts
>             _ -> throwError' $ err "Elim targeting wrong"  

Next we split the context |delta| into its parametric and
non-parametric parts, build and simplify the constraints, and convert
those that remain to equations.

>     let (delta0, delta1) = splitDelta lev' delta (map (\(_,_,ty) -> ty) elimTel)
>     elimTrace $ "Delta0: " ++ show delta0
>     elimTrace $ "Delta1: " ++ show delta1
>     let evPTy = ev _PTy
>     let (lev'', cs, xi) = buildConstraints lev evPTy evPTy (trail ts) B0 B0 
>     elimTrace $ "Initial constraints: " ++ show cs
>     elimTrace $ "Xi: " ++ show xi
>     (delta1, cs, goal) <- return $ simplifyConstraints lev'' delta1 (B0, cs <>> F0) goal
>     let eek = constraintsToEqns lev'' (trail cs)
>     elimTrace $ "Left over constraints: " ++ show eek

>     makeModule' NixHyps "elim" >> goIn
>     lenvDelta0 <- intros (trail delta0) []
>     makeModule "Motive"
>     goIn
>     lenv <- intros (trail xi) lenvDelta0

>     moduleToGoal SET
>     lenv <- pintros (trail delta1) lenv            

>     elimTrace $ "lenv: " ++ show lenv
>     lenv <- pintros eek lenv

>     motiveDef <- giveOutBelow ((lenv, INil) <:/> goal)
>     let delta0app = fmap (A . toBody . P) delta0
>     let motive = def motiveDef $$$ delta0app

>     elimTrace $ "motive: " ++ show motive

>     (tm, methodNames) <- createMethods delta0app ((_Pl, (lenvDelta0, INil) <:/> motive) : lenvDelta0)  methodTypes (elim $$. motive) B0
>     let tm'   = tm $$$ fmap (A . toBody . P) delta1
>         tm''  = tm' $$$ fmap (\ (_, (r :<: rty)) -> A (toBody (Refl rty r))) cs
>     elimTrace $ "TM'': " ++ show tm''

>     goOut
>     give tm''

>     return (trail methodNames)


> toMotive :: ProofState ()
> toMotive = goIn >> goIn >> goTop


This leaves us on the same goal we started with. For interactive use, we will
typically want to move to the first (lifted) method:

< toFirstMethod :: ProofState ()
< toFirstMethod = goIn >> goTop

We make elimination accessible to the user by adding it as a Cochon tactic:

