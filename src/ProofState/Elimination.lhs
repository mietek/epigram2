%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module ProofState.Elimination where

> import Control.Applicative
> import Data.Foldable hiding (sequence_)
> import Data.List
> import Data.Maybe
> import Debug.Trace

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import DisplayLang.DisplayTm
> import DisplayLang.Elaborator
> import DisplayLang.Naming

> import Evidences.Tm
> import Evidences.Rules hiding (simplify)

> import ProofState.ProofState
> import ProofState.ProofKit

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

$$\Gamma, \Delta \vdash e : (P : \Xi \rightarrow \Set) 
                            \rightarrow \vec{m} 
                            \rightarrow P \vec{t}$$

This eliminator, together with its type, is handled to the elimination
machinery in both term and value form. To reduce the boilerplate, we
use the following type synonym:

> type Eliminator = (INTM :=>: TY) :>: (INTM :=>: VAL)

And we will define |elim| this way:

< elim :: Maybe REF -> Eliminator -> ProofState ()
< elim comma eliminator = (...)




\subsection{Analyzing the eliminator}

Presented as a development, |elim| is called in the following context:

\begin{center}
\begin{alltt}
[ \((\Gamma)\) \(\rightarrow\) 
  \((\Delta)\) \(\rightarrow\)
] := ? : T
\end{alltt}
\end{center}

Where $\Gamma$ and $\Delta$ are introduced, and |T| is waiting to be
solved.

We have to analyze the eliminator we are given for two reasons. First,
we need to check that it \emph{is} an eliminator, that is:

\begin{itemize}

\item it has a motive, 

\item it has a bunch of methods, 

\item the target consists in the motive applied to some arguments

\end{itemize}

Second, we have to extract some vital piece of information from the
eliminator. Namely:

\begin{itemize} 

\item the type of the motive ($\Xi \rightarrow \Set$)

\item the arguments applied to the motive ($\vec{t}$)

\end{itemize}

To analyze the eliminator, we play a nice game. One option could be to
jump in a |draftModule|, introduce |lambdaBoys|, and retrieve and
check the different parts as we go along. However, this means that the
terms we get are built from references which will become out of
context, hence invalid. Therefore, we suffer the burden (and danger)
of carrying renaming of those terms.

The way we actually go is the following. The trick consists in
re-building the eliminator in the current development:

\begin{center}
\begin{alltt}
[ \((\Gamma)\) \(\rightarrow\) 
  \((\Delta)\) \(\rightarrow\)
  makeE [   \(P' \rightarrow\)
            \(m\sb{1} \rightarrow\)
            (...)
            \(m\sb{n} \rightarrow\)
            P := ? : \(\Xi \rightarrow *\)
            \(m\sb{1}\) := ? : \(M\sb{1}\) P
            (...)  
            \(m\sb{n}\) := ? : \(M\sb{n}\) P
  ] := e P \(\vec{m}\) : P \(\vec{t}\)
] := ? : T
\end{alltt}
\end{center}

Therefore, we will build the motive \emph{in-place}, instead of
analyzing the eliminator and then making the motive in two
phases. Moreover, we are able to safely check the shape of the
eliminator as well as extracting the interesting bits.

The development transformation is achieved by the following code:

> introElim :: Eliminator -> ProofState (Name, INTM :<: TY, [INTM], Bwd INTM)
> introElim (eType :>: e) = do
>     -- Make an (un-goaled) module
>     -- We will turn it in a (goaled T) girl at the end
>     elimName <- makeModule "makeE"
>     goIn
>     -- Get the type of the motive
>     -- And ask for making it real
>     let (motiveType, telType) = unPi $ valueOf eType
>     motiveTypeTm <- bquoteHere motiveType
>     p <- make $ "P" :<: motiveTypeTm
>     -- Get the type of the methods and the target
>     -- And ask for making them real
>     (ms, target) <- mkMethods $ telType $$ (A $ evTm p)
>     -- Check the motive, and target shape
>     checkMotive motiveType
>     checkTarget target p motiveType
>     -- Grab the terms which are applied to the motive
>     args <- matchArgs target motiveType
>     -- Close the problem (using the "made" subproblems!)
>     -- And go to the next subproblem, ie. making P
>     moduleToGoal target
>     giveNext $ N $ (termOf e :? termOf eType) $## (p : ms)
>     return (elimName, p :<: motiveType, ms, args)
>         where unPi :: VAL -> (VAL, VAL)
>               unPi (PI s t) = (s, t)

Above, we have used |mkMethods| to introduce the methods and retrieve
the target of the eliminator. Remember that the eliminator is
(supposed to be) a telescope of $\Pi$ types. To get the type of the
motive, we have deconstructed the first component of the telescope and
applied the motive to it. To get the methods, we simply iterate that
process, up to the point where all the $\Pi$s have been consummed.

> mkMethods :: TY -> ProofState ([INTM], INTM)
> mkMethods = mkMethods' []
>     where mkMethods' :: [INTM] -> TY -> ProofState ([INTM], INTM)
>           mkMethods' ms t = 
>               case t of 
>                 PI s t -> do
>                     sTm <- bquoteHere s
>                     m <- make $ "m" :<: sTm
>                     mkMethods' (m : ms) (t $$ (A $ evTm m))
>                 target -> do
>                     targetTm <- bquoteHere target
>                     return (reverse ms, targetTm)

Another helper function has been |matchArgs|. We know that the target
is the following term:

$$P \vec{t}$$

Hence, |matchArgs| is given the target as well as the telescope-type
of |P|. |matchArgs| deconstructs recursively the telescope,
accumulating the arguments of the target along the way. When reaching
|Set|, we have accumulated all arguments of |P|.

> matchArgs :: INTM -> VAL -> ProofState (Bwd INTM)
> matchArgs _ SET = return B0
> matchArgs (N (t :$ A x)) (PI s r) = 
>   freshRef ("s" :<: s) $ \y -> do
>       args <- matchArgs (N t) (r $$ (A $ pval y))
>       return $ args :< x
>       


\subsubsection{Checking the eliminator}

The calls to |checkMotive|, and |checkTarget| are here to ensure that
we are handed "stuffs" which fit our technology. They are mostly dull
at the moment, because we only have nice users.

|checkMotive| consists in veryfing that the motive is of type:

$$P : \Xi \rightarrow *$$

> checkMotive :: VAL -> ProofState ()
> checkMotive SET = return ()
> checkMotive (PI s t) =
>     freshRef ("s" :<: s) $ \x ->
>         checkMotive (t $$ (A $ pval x))
> checkMotive _ = throwError' "elimination: your motive is suspicious"


On the other hand, |checkTarget| consists in verifying that the target
consists of the motive applied to some stuff. Note that |checkTarget|
is a |matchArgs| on paranoid. 

> checkTarget :: INTM -> INTM -> VAL -> ProofState ()
> checkTarget goal motive motiveType = checkTarget' (evTm goal) motiveType 
>     where checkTarget' :: VAL -> VAL -> ProofState ()
>           checkTarget' goal SET = do
>               isEqual <- withNSupply $ equal (motiveType :>: (goal, evTm motive))
>               case isEqual of
>                 True -> return ()
>                 False -> throwError' "elimination: your target is not using the motive?!"
>           checkTarget' (N (f :$ A _)) (PI s t) = do
>               freshRef ("s" :<: s) $ \x ->
>                   checkTarget' (N f) (t $$ (A $ pval x))
>           checkTarget' _ _ = throwError' "eliminator: your target is suspicious"

\pierre{There are also some conditions on the variables that can be used in
these terms! I have to look that up too. This is a matter of traversing the
terms to collect the |REF|s in them and check that they are of the right
domains.}


\subsection{Making the motive}

The |introElim| command have kindly generated a subgoal for the motive as well
as subgoals for the methods. Doing that, it has also brought us to the subgoal
consisting of making |P|. That's a good think because this is what we are
going to do.

First, remember the type of the motive:

$$P : \Xi \rightarrow \Set$$

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

> renameVar :: Name -> REF -> INTM -> INTM
> renameVar n r' t
>     = fmap (\r@(rn := _) -> if rn == n then r' else r) t

> collectRefs :: INTM -> [REF]
> collectRefs r = foldMap (\x -> [x]) r

> usedIn = Data.Foldable.elem

> extractDelta1 :: Bwd REF -> [INTM] -> ProofState (Fwd REF)
> extractDelta1 delta argTypes = 
>     let deps = foldMap collectRefs argTypes in
>     extractDelta1' delta deps

> extractDelta1' :: Bwd REF -> [REF] -> ProofState (Fwd REF)
> extractDelta1' (rs :< r) deps | r `usedIn` deps = do
>     -- r is used in the motive or methods
>     rTyTm <- bquoteHere $ pty r
>     -- Add its components to the dependency set
>     let deps' = deps `union` collectRefs rTyTm
>     -- Drop it from Delta1
>     extractDelta1' rs deps'
>                               | otherwise = do
>     -- r is not used
>     -- Get delta1'
>     delta1' <- extractDelta1' rs deps
>     -- And add it to it                   
>     return $ r :> delta1'
> extractDelta1' B0 deps = return F0


> type Binder = (Name :<: INTM)
> type Binders = Bwd Binder

> toBinder :: REF -> NameSupply -> Binder
> toBinder (n := ( _ :<: t)) = (| (n :<:) (bquote B0 t) |)

> toBinders :: [REF] -> NameSupply -> Binders
> toBinders rs =  (sequence $ fmap toBinder rs) 
>                 >>= (return . bwdList)


> type Constraints = Bwd (REF, INTM :>: INTM)

> mapSnd :: (b -> c) -> (a,b) -> (a,c)
> mapSnd f (x,y) = (x, f y)

> mapBoth :: (a -> b) -> (a :>: a) -> (b :>: b)
> mapBoth f (x :>: y) = f x :>: f y

> simplify ::  Binders -> 
>              Constraints -> 
>              (TY, TY, [(REF, INTM)]) -> 
>              INTM -> 
>              NameSupply -> (Binders, Constraints, INTM)
> simplify delta1 constraints (SET, SET, []) goal = return (delta1, constraints, goal)
> simplify delta1 constraints (PI s t, PI s' t', (x@(xn := _),p) : xts) goal = do
>     isSequalS' <- equal $ SET :>: (s, s')
>     let delta10Delta11 = whereFound (unNP p) delta1
>     (case p of
>       NP y | isJust delta10Delta11 && isSequalS' -> do
>         let  Just (delta10, delta11) = delta10Delta11
>              (delta1', renamer) = collapse delta10 (xn `renameVar` y) delta11
>         simplify  delta1' 
>                   (fmap (mapSnd $ mapBoth renamer) constraints)
>                   (t $$ (A $ pval x), t' $$ (A $ pval x), fmap (mapSnd renamer) xts)
>                   (renamer goal)
>       _ -> do
>         s'Tm <- bquote B0 s'
>         simplify  delta1 
>                   (constraints :< (x, s'Tm :>: p)) 
>                   ((t $$ A (pval x)), t' $$ A (pval x), xts)
>                   goal) :: NameSupply -> (Binders, Constraints, INTM)
>     where  unNP :: INTM -> REF
>            unNP (NP y) = y

> collapse :: Bwd Binder -> (INTM -> INTM) -> Fwd Binder -> (Bwd Binder, (INTM -> INTM))
> collapse delta1 renamer F0 = (delta1, renamer)
> collapse delta1 renamer ((n :<: _S) :> e) = 
>     let _S' = renamer _S
>         y = n := (DECL :<: evTm _S')
>     in
>       collapse (delta1 :< (n :<: _S')) ((n `renameVar` y) . renamer) e

> whereFound :: REF -> Binders -> Maybe (Bwd Binder, Fwd Binder)
> whereFound _ B0 = Nothing
> whereFound x@(n := _) (xs :< r@(xn :<: _)) | n == xn = 
>     return (B0, xs <>> F0)
>                                      | otherwise = do
>     (left, right) <- whereFound x xs
>     return (left :< r, right)


Finally, we can make the motive, that is close that subgoal. This simply
consists in chaining the commands above, and give the computed term. Unless
I've screwed up things, |give| should always be happy.

> makeMotive :: TY -> VAL -> [REF] -> [INTM] -> Bwd INTM -> ProofState ([REF], INTM)
> makeMotive xi goal deltas argTypes args = do
>   -- Extra delta1 from delta
>   deltas <- extractDelta1 (bwdList deltas) argTypes
>   -- Transform Delta into Binder form
>   binders <- withNSupply $ toBinders $ trail deltas
>   -- Make the whole list of constraints
>   xis <- introMotive 
>   let constraintsI = zip xis (trail args)
>   let triple = (xi, xi, constraintsI)
>   -- Get goal in Term form
>   goalTm <- bquoteHere goal
>   -- Simplify that mess
>   (binders, constraints, goal) <- withNSupply $ simplify binders B0 triple goalTm
>   -- Introduce Delta
>   deltas <- sequence $ map (\t -> piBoy $ "delta" :<: t) (map (\(_ :<: t) -> t) (trail binders))
>   -- Make (xi == ti) -> T
>   solution <- withNSupply $ makeEq constraints goal
>   -- Rename solution on fresh Delta
>   let motiv = rename (map (\(n :<: _) -> n) (trail binders)) deltas solution
>   motive <- give motiv
>   return (deltas, motive)

> rename :: [Name] -> [REF] -> INTM -> INTM
> rename [] [] t = t
> rename (n : ns) (r : rs) t = rename ns rs (renameVar n r t)

> makeEq :: Bwd (REF, INTM :>: INTM) -> INTM -> NameSupply -> INTM
> makeEq B0 t = return t
> makeEq (cstrt :< (r, sTy :>: s)) t = do
>   rTy <- bquote B0 (pty r)
>   makeEq cstrt (ARR (PRF (EQBLUE (rTy :>: NP r) (sTy :>: s))) t)

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

> mkRefls :: [INTM] -> VAL -> NameSupply -> [INTM]
> mkRefls (t : args) (PI s s') r = (N $ (P refl) $## [ bquote B0 s r 
>                                                    , t ])
>                                  : mkRefls args (s' $$ (A (evTm t))) r
> mkRefls [] SET r = []


Then, it is straightforward to build the term we want and to give it:

> applyElim :: Name -> INTM -> [INTM] -> [REF] -> ([INTM] :<: VAL) -> ProofState ()
> applyElim elim motive methods deltas (args :<: xi) = do
>     reflArgs <- withNSupply $ mkRefls args xi
>     Just (N e) <- lookupName elim
>     giveNext $ N $ e $## (map NP deltas ++
>                           reflArgs)
>     return ()

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

> elimDoctor :: [REF] -> VAL -> Eliminator -> ProofState (Name, INTM, [INTM], [REF], [INTM] :<: VAL)
> elimDoctor deltas goal eliminator = do
>     -- Prepare the development by creating subgoals:
>     --    1/ the motive
>     --    2/ the methods
>     --    3/ the arguments of the motive
>     (eliminator, motive :<: xi, methods, args) <- introElim eliminator
>     -- Build the motive
>     (deltas, motive) <- makeMotive xi goal deltas (motive : methods) args
>     -- Leave the development with the methods unimplemented
>     goOut
>     return (eliminator, motive, methods, deltas, trail args :<: xi)

In a third part, we solve the problem. To that end, we simply have to use the
|applyElim| command we have developed above.

Therefore, we get the |elim| commands, the one, the unique. It is simply a
Frankenstein operation of these three parts:

> elim :: Maybe REF -> Eliminator -> ProofState ()
> elim Nothing eliminator = do -- Nothing: no comma
>     -- Where are we?
>     (deltas, goal) <- elimContextGoal
>     -- What is the eliminator?
>     (eliminator, motive, methods, deltas, args) <- 
>         elimDoctor deltas goal eliminator
>     -- Apply the motive, ie. solve the goal
>     applyElim eliminator motive methods deltas args


We make elimination accessible to the user by adding it as a Cochon tactic:

> elimCTactic :: ExDTmRN -> ProofState String
> elimCTactic r = do 
>     (elimTy :>: e) <- elabInfer r
>     elimTyTm <- bquoteHere elimTy
>     elim Nothing ((elimTyTm :=>: elimTy) :>: (N e :=>: (evTm (N e))))
>     return "Elimination occured. Subgoals awaiting work..."

> import -> CochonTactics where
>   : unaryExCT "eliminate" elimCTactic
>       "eliminate <name> - eliminates with a motive."