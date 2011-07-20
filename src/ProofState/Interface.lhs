\section{The |ProofState| Kit}
\label{sec:ProofState.Interface}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface where

> import Control.Monad.Error
> import Control.Applicative
> import Data.Foldable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Structure
> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.TypeChecker
> import Evidences.ErrorHandling

> import {-# SOURCE #-} Elaboration.Wire

> import Kit.NatFinVec

%endif

> chkPS :: (TY :>: EXP) -> ProofState ()
> chkPS (ty :>: e) = do
>  lev <- getDevLev
>  chk lev (ty :>: (ENil, e))


The proof state lives on a rich substrate of operations, inherited
from the |ProofContext| as well as the |ProofState| monad. In this
module, we export these operations as part of the Interface.



\subsection{Accessing the |NameSupply|}


By definition of the |Development| in
Section~\ref{sec:ProofState.Structure.Developments}, we have that
every entry is associated a namespace by the mean of a local name
supply. As a result, the |ProofState| can almost be made a
|NameSupplier|. The exception being that it cannot fork the name
supply, because it cannot generates new namespaces.

> instance NameSupplier ProofState where
>     freshName s f = do
>         nsupply <- getDevNSupply
>         freshName s ( \n nsupply' -> do
>             putDevNSupply nsupply'
>             f n
>           ) nsupply
>
>     forkNSupply = error "ProofState does not provide forkNSupply"
>     
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply to
proof state commands.

> withNSupply :: (NameSupply -> x) -> ProofState x
> withNSupply f = getDevNSupply >>= return . f

\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


\subsection{Accessing the type-checker}



> checkHere :: (TY :>: EXP) -> ProofState ()
> checkHere = chkPS

> inferHere :: EXP -> ProofState TY
> inferHere tt = getDevLev >>= \ l -> inf l (ENil, tt)

> inferSpHere :: (EXP :<: TY) -> [Elim EXP] -> ProofState TY
> inferSpHere ety es = getDevLev >>= \ l -> spInf l ety (ENil , es)



\subsection{Being paranoiac}


The |validateHere| command performs some sanity checks on the current
location, which may be useful for paranoia purposes.

< validateHere :: ProofState ()
< validateHere = do
<     m <- getCurrentEntry
<     case m of
<         CDefinition _ (_ := DEFN tm :<: ty) _ _ _ -> do
<             ty' <- bquoteHere ty
<             checkHere (SET :>: ty')
<                 `pushError`  (err "validateHere: definition type failed to type-check: SET does not admit"
<                              ++ errTyVal (ty :<: SET))
<             tm' <- bquoteHere tm
<             checkHere (ty :>: tm')
<                 `pushError`  (err "validateHere: definition failed to type-check:"
<                              ++ errTyVal (ty :<: SET)
<                              ++ err "does not admit"
<                              ++ errTyVal (tm :<: ty))
<             return ()
<         CDefinition _ (_ := HOLE _ :<: ty) _ _ _ -> do
<             ty' <- bquoteHere ty
<             checkHere (SET :>: ty')
<                 `pushError`  (err "validateHere: hole type failed to type-check: SET does not admit" 
<                              ++ errTyVal (ty :<: SET))
<             return ()
<         _ -> return ()


> validateHere :: ProofState ()
> validateHere = return () -- ha ha ha ha




\subsection{Making modules}

A module is a pretty dull thing: it is just a name and a
development. As far as I know, there are three usages of modules. The
first one is the one we are used to: introducing namespaces and
avoiding name clashes. This is mostly used at the programming
level. For making modules, we use |makeModule|.

> makeModule :: String -> ProofState Name
> makeModule s = do
>     nsupply <- getDevNSupply
>     inScope <- getInScope
>     let n = mkName nsupply s
>     -- Insert a new entry above, the empty module |s|
>     let dev = Dev {  devEntries       =  B0
>                   ,  devTip           =  Module 
>                   ,  devNSupply       =  freshNSpace nsupply s
>                   ,  devSuspendState  =  SuspendNone 
>                   ,  devLevelCount    =  boys inScope
>                   ,  devHypState      =  InheritHyps
>                   }
>     putEntryAbove $ EModule  {  name   =  n 
>                              ,  dev    =  dev}
>     putDevNSupply $ freshen nsupply
>     return n
>  where 
>    boys :: Entries -> Int
>    boys B0 = 0
>    boys (es :< EParam _ _ _ _) =  1 + boys es 
>    boys (es :< _) =  boys es 


The second usage is more technical, and occurs exclusively in the
implementation (such as in tactics, for instance). It consists in
making a module, going in it, doing some constructions and analyses,
and at some stage wanting to say that this module is actually an open
definition of a certain type (a goal). Turning a module into a goal is
implemented by |moduleToGoal|. An instance of this pattern appears in
Section~\ref{subsec:Tactics.Elimination.analysis}.

> moduleToGoal :: EXP -> ProofState EXP
> moduleToGoal e = (| snd (moduleToGoal' e) |)

> moduleToGoal' :: EXP -> ProofState (DEF,EXP)
> moduleToGoal' ty = do
>     chkPS (SET :>: ty) `pushError` err "moduleToGoal: not a set"
>     CModule _ <- getCurrentEntry
>     putDevTip $ Unknown ty Waiting
>     updateDefFromTip


The last usage of modules is to mess around: introducing things in the
proof context to later, in one go, remove it all. One need to be
extremely careful with the removed objects: the risk of introducing
dangling references is high.


> draftModule :: String -> ProofState t -> ProofState t
> draftModule name draftyStuff = do
>     makeModule name
>     goIn
>     t <- draftyStuff
>     goOutBelow
>     mm <- removeEntryAbove
>     case mm of
>         Just (EModule _ _) -> return t
>         _ -> throwError' . err $ "draftModule: drafty " ++ name
>                                  ++ " did not end up in the right place!"




\subsection{Making goals}


The |make| command adds a named goal of the given type above the
cursor. The meat is actually in |makeKinded|, below.

> make :: (String :<: TY) -> ProofState EXP
> make = makeKinded Nothing Waiting

When making a new definition, the reference to this definition bears a
\emph{hole kind}
(Section~\ref{subsec:Evidences.Tm.references}). User-generated goals
are of kind |Waiting|: waiting for the user to solve it (or, if lucky,
an automation tool could nail it down). For making these kind of
definition, we will use the |make| command above. However, during
Elaboration for instance (Section~\ref{sec:Elaborator.Elaborator}),
the proof system will insert goals itself, with a somewhat changing
mood such as |Hoping| or |Crying|.

> makeKinded :: Maybe String ->  HKind -> (String :<: TY) -> 
>                                ProofState EXP
> makeKinded manchor holeKind (name :<: ty) = do
>     -- Check that the type is indeed a type
>     checkHere (SET :>: ty) 
>                     `pushError`  
>                     (err "make: " ++ errTm ty ++ err " is not a set.")
>     -- Make a name for the goal, from |name|
>     nsupply <- getDevNSupply
>     goalName <- pickName "Goal" name
>     let  n  =  mkName nsupply goalName
>     -- Make a reference for the goal, with a lambda-lifted type
>     inScope <- getInScope
>     let  binScope  = boys inScope
>          liftedTy = bwdVec (boys inScope)
>                             (\ n ys -> piLift n ys) ty
>          def = DEF n liftedTy Hole

<  (eats (trail (fmap (\(_,s,_) -> s) (boys inScope))) Hole)

>     -- Make an entry for the goal, with an empty development
>     let dev = Dev  {  devEntries       =  B0
>                    ,  devTip           =  Unknown ty holeKind
>                    ,  devNSupply       =  freshNSpace nsupply goalName
>                    ,  devSuspendState  =  SuspendNone
>                    ,  devLevelCount    =  bwdLength binScope
>                    ,  devHypState      =  InheritHyps
>                    }
>     -- Put the entry in the proof context
>     putDevNSupply $ freshen nsupply
>     putEntryAbove $ EDef def dev Nothing
>     -- Return a reference to the goal
>     return $  (D def :$ B0) $$$ fmap (\x -> A (P x :$ B0)) binScope
>  where 
>    boys :: Entries -> Bwd (Int, String, TY)
>    boys B0 = B0
>    boys (es :< EParam _ s t l) =  boys es :< (l, s, t)
>    boys (es :< _) =  boys es 






\subsection{Giving a solution}


The |give| command takes a term and solves the current goal with it,
if it type-checks. At the end of the operation, the cursor has not
moved: we are still under the goal, which has now been |Defined|. Note
that entries below the cursor are (lazily) notified of the good news.

> give :: EXP -> ProofState DEF
> give tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown tipTy hk -> do
>             -- Working on a goal
>
>             -- Check that |tm| is of the expected type
>             chkPS (tipTy :>: tm) 
>                 `pushError`
>                 (err "give: typechecking failed:" ++ errTm tm
>                  ++ err "is not of type" ++ errTyTm (SET :>: tipTy))

>             -- Update the entry as Defined, together with its definition
>             putDevTip $ Defined (tipTy :>: tm)
>             (def', _) <- updateDefFromTip

>             -- Propagate the good news
>             updateDef def'

>             -- Return the reference
>             return def'
>         _  -> throwError' $ err "give: only possible for incomplete goals."

For convenience, we combine giving a solution and moving. Indeed,
after |give|, the cursor stands in a rather boring position: under a
|Defined| entry, with no work to do. So, a first variant is
|giveOutBelow| that gives a solution and moves just below the
now-defined entry. A second variant is |giveNext| that gives as well
and moves to the next goal, if one is available.

> giveOutBelow :: EXP -> ProofState DEF
> giveOutBelow tm = give tm <* goOutBelow
>
> giveNext :: EXP -> ProofState DEF
> giveNext tm = give tm <* (nextGoal <|> goOut)




\subsection{|\|-abstraction}


When working at solving a goal, we might be able to introduce an
hypothesis. For instance, if the goal type is \(\Nat \To \Nat \To
\Nat\), we can introduce two hypotheses \(\V{x}\) and
\(\V{y}\). Further, the type of the goal governs the kind of the
parameter (a lambda, or a forall) and its type. This automation is
implemented by |lambdaParam| that lets you introduce a parameter above
the cursor while working on a goal.

> lambdaParam :: String -> ProofState (Tm {Head, s, Z})
> lambdaParam x = do
>     tip <- getDevTip
>     case tip of
>       Unknown ty hk ->
>         case lambdable (ev ty) of
>           Just (k, s, t) -> do
>               -- Insert the parameter above the cursor
>               l <- getDevLev
>               putEntryAbove $ EParam k x s l
>               putDevLev (succ l)
>               -- Update the Tip
>               let tipTy = t (P (l, x, s) :$ B0)
>               putDevTip $ Unknown tipTy hk
>               (d,_) <- updateDefFromTip
>               -- Return the reference to the parameter
>               return $ P (l, x, s)
>           _  -> throwError' $ err "lambdaParam: goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaParam: only possible for incomplete goals."


\subsection{Assumptions}

With |lambdaParam|, we can introduce parameters under a proof
goal. However, when working under a module, we would like to be able
to introduce hypothesis of some type. This corresponds to some kind of
``Assume'' mechanism, where we assume the existence of an object of
the provided type under the given module.

> assumeParam :: (String :<: TY) -> ProofState (Tm {Head, s, Z})
> assumeParam (x :<: ty)  = do
>     tip <- getDevTip
>     case tip of
>       Module -> do
>         l <- getDevLev
>         -- Simply make the reference
>         putEntryAbove $ EParam ParamLam x ty l
>         putDevLev (succ l)
>         return $ P (l, x, ty) 
>       _    -> throwError' $ err "assumeParam: only possible for modules."

\subsection{|Pi|-abstraction}

When working at defining a type (an object in |Set|), we can freely
introduce |Pi|-abstractions. This is precisely what |piParam| let us
do.

> piParam :: (String :<: EXP) -> ProofState (Tm {Head, s, Z})
> piParam (s :<: ty) = do
>   chkPS (SET :>: ty) `pushError` err "piParam: domain is not a set"
>   piParamUnsafe $ s :<: ty

The variant |piParamUnsafe| will not check that the proposed type is
indeed a type, so it requires further attention.

> piParamUnsafe :: (String :<: TY) -> ProofState (Tm {Head, s, Z})
> piParamUnsafe (s :<: ty) = do
>     tip <- getDevTip
>     case tip of
>         Unknown SET hk -> do
>           -- Working on a goal of type |Set|
>           l <- getDevLev
>           -- Simply introduce the parameter
>           putEntryAbove $ EParam ParamPi s ty l
>           putDevLev (succ l)
>           return $ P (l, s, ty)
>         Unknown _ _ -> throwError' $ err "piParam: goal is not of type SET."
>         _           -> throwError' $ err "piParam: only possible for incomplete goals."



\subsection{Binding a type}

The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Entries -> EXP -> EXP
> liftType es = liftType' (bwdList $ foldMap param es) 
>   where param (EParam _ s t l) = [(l, s, t)]
>         param _ = []

> liftType' :: Bwd (Int, String, TY) -> EXP -> EXP
> liftType' es t = bwdVec es
>   (\ n ys -> piLift {n} ys t)



\subsection{Name management}

The |lookupName| function looks up a name in the context (including axioms and
primitives -- eventually);

> lookupName :: Name -> ProofState (Maybe EXP)
> lookupName name = do
>     inScope <- getInScope
>     case find ((Just name ==) . entryName) inScope of
>       Just (EDef d _ _)  -> return $ Just $ applySpine (def d) inScope 
>       Nothing             -> return Nothing 

<         case find ((name ==) . refName . snd) primitives of
<           Just (_, ref)  -> return $ Just $ applySpine ref inScope
<           Nothing        -> return Nothing

The |pickName| command takes a prefix suggestion and a name suggestion
(either of which may be empty), and returns a more-likely-to-be-unique
name if the name suggestion is empty.

> pickName :: String -> String -> ProofState String
> pickName "" s = pickName "x" s
> pickName prefix ""  = do
>     m <- getCurrentName
>     r <- getDevNSupply
>     return $ prefix ++ show (foldMap snd m + snd r)
> pickName _ s   = return s

> 
