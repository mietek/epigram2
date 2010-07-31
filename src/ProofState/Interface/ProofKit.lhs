\section{The |ProofState| Kit}
\label{sec:proof_state_kit}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.ProofKit where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import ProofState.Edition.ProofContext
> import ProofState.Edition.News
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Lifting
> import ProofState.Interface.NameResolution

> import DisplayLang.DisplayTm
> import DisplayLang.Name

We have to use a boot file to resolve the circular dependency between this module
and |Elaboration.Wire|. We need to make calls to the news propagation code from
navigation commands, but the news code uses proof state manipulation commands
defined here.

> import {-# SOURCE #-} Elaboration.Wire

> import Evidences.Tm
> import Evidences.Rules

%endif

\question{There are some serious re-ordering of functions to be done
here, in order to improve the narrative.}


\subsection{Asking for Evidence}

A |ProofState| is almost a |NameSupplier|, but it cannot fork the
name supply.

> instance NameSupplier (ProofStateT e) where
>     freshRef (s :<: ty) f = do
>         nsupply <- getDevNSupply
>         freshRef (s :<: ty) (\ref nsupply' -> do
>             putDevNSupply nsupply'
>             f ref
>           ) nsupply
>
>     forkNSupply = error "ProofState does not provide forkNSupply"
>     
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply
to proof state commands.

> withNSupply :: (NameSupply -> x) -> ProofState x
> withNSupply f = getDevNSupply >>= return . f

\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


The |bquoteHere| command $\beta$-quotes a term using the current name supply.

> bquoteHere :: Tm {d, VV} REF -> ProofState (Tm {d, TT} REF)
> bquoteHere tm = withNSupply $ bquote B0 tm


> runCheckHere :: (ErrorTok e -> ErrorTok DInTmRN) -> Check e a -> ProofState a
> runCheckHere f c = do
>     me <- withNSupply $ liftError' f . typeCheck c
>     lift me


Similarly, |checkHere| type-checks a term using the local name supply...

> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere tt = runCheckHere (fmap DTIN) $ check tt

... and |inferHere| infers the type of a term using the local name supply.

> inferHere :: EXTM -> ProofState (VAL :<: TY)
> inferHere tm = runCheckHere (fmap DTIN) $ infer tm



The |validateHere| performs some checks on the current location, which
may be useful for paranoia purposes.

> validateHere :: ProofState ()
> validateHere = do
>     m <- getCurrentEntry
>     case m of
>         CDefinition _ (_ := DEFN tm :<: ty) _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: girl type failed to type-check: SET does not admit"
>                              ++ errTyVal (ty :<: SET))
>             tm' <- bquoteHere tm
>             checkHere (ty :>: tm')
>                 `pushError`  (err "validateHere: definition failed to type-check:"
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "does not admit"
>                              ++ errTyVal (tm :<: ty))
>             return ()
>         CDefinition _ (_ := HOLE _ :<: ty) _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: hole type failed to type-check: SET does not admit" 
>                              ++ errTyVal (ty :<: SET))
>             return ()
>         _ -> return ()


> withGoal :: (VAL -> ProofState ()) -> ProofState ()
> withGoal f = do
>   (_ :=>: goal) <- getGoal "withGoal"
>   f goal





The |goTo| command moves the focus to the entry with the given long name,
starting from the root module.

> goTo :: Name -> ProofState ()
> goTo name = goRoot >> goTo' name
>   where
>     goTo' :: Name -> ProofState ()
>     goTo' [] = return ()
>     goTo' (xn:xns) = (seek xn >> goTo' xns)
>         `pushError` (err "goTo: could not find " ++ err (showName (xn:xns)))
>
>     seek :: (String, Int) -> ProofState ()
>     seek xn = do
>         goIn
>         m <- getCurrentName
>         if xn == last m
>             then return ()
>             else goUp `untilA` (guard . (== xn) . last =<< getCurrentName)


\subsection{Goal Search Commands}

The |isGoal| command succeeds (returning |()|) if the current location is a goal,
and fails (yielding |Nothing|) if not.

> isGoal :: ProofState ()
> isGoal = do
>     Unknown _ <- getDevTip
>     return ()


We can now compactly describe how to search the proof state for goals, by giving
several alternatives for where to go next and continuing until a goal is reached.

> prevStep :: ProofState ()
> prevStep = ((goUp >> much goIn) <|> goOut) `pushError` (err "prevStep: no previous steps.")
>
> prevGoal :: ProofState ()
> prevGoal = (prevStep `untilA` isGoal) `pushError` (err "prevGoal: no previous goals.")
>
> nextStep :: ProofState ()
> nextStep = ((goIn >> goTop) <|> goDown <|> (goOut `untilA` goDown))
>                `pushError` (err "nextStep: no more steps.")
>
> nextGoal :: ProofState ()
> nextGoal = (nextStep `untilA` isGoal) `pushError` (err "nextGoal: no more goals.")


Sometimes we want to stay at the current location if it is a goal, and go
to the next goal otherwise.

> seekGoal :: ProofState ()
> seekGoal = isGoal <|> nextGoal


\subsection{Module Commands}


> makeModule :: String -> ProofState Name
> makeModule s = do
>     n <- withNSupply (flip mkName s)
>     nsupply <- getDevNSupply
>     putEntryAbove (EModule n (Dev B0 Module (freshNSpace nsupply s) SuspendNone))
>     putDevNSupply (freshName nsupply)
>     return n

> moduleToGoal :: INTM -> ProofState (EXTM :=>: VAL)
> moduleToGoal ty = do
>     (_ :=>: tyv) <- checkHere (SET :>: ty)
>     CModule n <- getCurrentEntry
>     inScope <- getInScope
>     let  ty' = liftType inScope ty
>          ref = n := HOLE Waiting :<: evTm ty'
>     putCurrentEntry (CDefinition LETG ref (last n) ty')
>     putDevTip (Unknown (ty :=>: tyv))
>     return (applySpine ref inScope)

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


The |lookupName| function looks up a name in the context (including axioms and
primitives); if found, it returns the reference applied to the spine of
shared parameters.

> lookupName :: Name -> ProofStateT e (Maybe (EXTM :=>: VAL))
> lookupName name = do
>     inScope <- getInScope
>     case Data.Foldable.find ((name ==) . entryName) inScope of
>       Just (EEntity ref _ _ _)  -> return (Just (applySpine ref inScope))
>       Nothing             ->
>         case Data.Foldable.find ((name ==) . refName . snd) primitives of
>           Just (_, ref)  -> return (Just (applySpine ref inScope))
>           Nothing        -> return Nothing



\subsection{Construction Commands}

Various commands yield an |EXTM :=>: VAL|, and we sometimes need to convert
this to an |INTM :=>: VAL|:

> neutralise :: Monad m => (EXTM :=>: VAL) -> m (INTM :=>: VAL)
> neutralise (n :=>: v) = return (N n :=>: v)

The |apply| command checks if the last entry in the development is a girl $y$ with type
$\Pi S T$ and if so, adds a goal of type $S$ and applies $y$ to it.

> apply :: ProofState (EXTM :=>: VAL)
> apply = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF ref@(name := k :<: (PI s t)) _ _ _ _ -> do
>         s' <- bquoteHere s
>         t' <- bquoteHere (t $$ A s)
>         z :=>: _ <- make ("z" :<: s')
>         make ("w" :<: t')
>         goIn
>         give (N (P ref :$ A (N z)))
>     _ -> throwError' $ err  $ "apply: last entry in the development" 
>                             ++ " must be a girl with a pi-type."

The |done| command checks if the last entry in the development is a girl, and if so,
fills in the goal with this entry.

> done :: ProofState (EXTM :=>: VAL)
> done = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF ref _ _ _ _ -> give (N (P ref))
>     _ -> throwError' $ err "done: last entry in the development must be a girl."

The |give| command checks the provided term has the goal type, and if so, fills in
the goal, updates the reference and goes out. The |giveNext| variant moves to the
next goal (if one exists) instead.

> give :: INTM -> ProofState (EXTM :=>: VAL)
> give tm = give' tm <* goOutBelow

> giveNext :: INTM -> ProofState (EXTM :=>: VAL)
> giveNext tm = give' tm <* (nextGoal <|> goOut)

> give' :: INTM -> ProofState (EXTM :=>: VAL)
> give' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             checkHere (tipTy :>: tm) `pushError`
>                 (err "give: typechecking failed:" ++ errTm (DTIN tm)
>                  ++ err "is not of type" ++ errTyVal (tipTy :<: SET))
>             aus <- getGlobalScope
>             sibs <- getEntriesAbove
>             let tmv = evTm (parBind aus sibs tm)
>             CDefinition kind (name := _ :<: tyv) xn ty <- getCurrentEntry
>             let ref = name := DEFN tmv :<: tyv
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             putCurrentEntry (CDefinition kind ref xn ty)
>             updateRef ref
>             return (applySpine ref aus)
>         _  -> throwError' $ err "give: only possible for incomplete goals."

The |lambdaBoy| command checks that the current goal is a $\Pi$-type, and if so,
appends a $\lambda$-abstraction with the appropriate type to the current development.

> lambdaBoy :: String -> ProofState REF
> lambdaBoy x = do
>     tip <- getDevTip
>     case tip of
>       Unknown (pi :=>: ty) -> case lambdable ty of
>         Just (k, s, t) -> freshRef (x :<: s) (\ref -> do
>             s' <- bquoteHere s
>             putEntryAbove (EPARAM ref (mkLastName ref) k s')
>             let tipTyv = t (pval ref)
>             tipTy <- bquoteHere tipTyv
>             putDevTip (Unknown (tipTy :=>: tipTyv))
>             return ref
>           )
>         _  -> throwError' $ err "lambdaBoy: goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaBoy: only possible for incomplete goals."

The |lambdaBoy'| variant allows a type to be specified, so it can
be used with modules. If used at an |Unknown| tip, it will check
that the supplied type matches the one at the tip.

> lambdaBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> lambdaBoy' (x :<: (ty :=>: tv))  = do
>     tip <- getDevTip
>     case tip of
>       Module -> freshRef (x :<: tv) (\ref -> do
>           putEntryAbove (EPARAM ref (mkLastName ref) ParamLam ty)
>           return ref
>         )
>       Unknown (pi :=>: gty) -> case lambdable gty of
>         Just (k, s, t) -> do
>           eq <- withNSupply (equal (SET :>: (tv, s)))
>           if eq
>             then freshRef (x :<: tv) (\ref -> do
>                 putEntryAbove (EPARAM ref (mkLastName ref) k ty)
>                 let tipTyv = t (pval ref)
>                 tipTy <- bquoteHere tipTyv
>                 putDevTip (Unknown (tipTy :=>: tipTyv))
>                 return ref
>               )
>             else throwError' $ err "lambdaBoy': given type does not match domain of goal."
>         _  -> throwError' $ err "lambdaBoy': goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaBoy': only possible for modules or incomplete goals."


The following piece of kit might profitably be shifted to somewhere more
general.

> lambdable :: TY -> Maybe (ParamKind, TY, VAL -> TY)
> lambdable (PI s t)         = Just (ParamLam, s, (t $$) . A)
> lambdable (PRF (ALL s p))  = Just (ParamAll, s, \v -> PRF (p $$ A v))
> lambdable _                = Nothing


The |make| command adds a named goal of the given type to the bottom of the
current development, after checking that the purported type is in fact a type.

> make :: (String :<: INTM) -> ProofState (EXTM :=>: VAL)
> make = make' Waiting

> make' :: HKind -> (String :<: INTM) -> ProofState (EXTM :=>: VAL)
> make' hk (s :<: ty) = do
>     _ :=>: tyv <- checkHere (SET :>: ty) `pushError`  (err "make: " 
>                              ++ errTm (DTIN ty)
>                              ++ err " is not a set.")
>     inScope <- getInScope
>     s' <- pickName "G" s
>     n <- withNSupply (flip mkName s')
>     let  ty'  = liftType inScope ty
>          ref  = n := HOLE hk :<: evTm ty'
>     nsupply <- getDevNSupply
>     let dev = Dev B0 (Unknown (ty :=>: tyv)) (freshNSpace nsupply s') SuspendNone
>     putEntryAbove (EDEF ref (last n) LETG dev ty')
>     putDevNSupply (freshName nsupply)
>     return (applySpine ref inScope)


The |pickName| command takes a prefix suggestion and a name suggestion
(either of which may be empty), and returns a more-likely-to-be-unique
name if the name suggestion is empty.

> pickName :: String -> String -> ProofState String
> pickName "" s = pickName "x" s
> pickName prefix ""  = do
>     m <- getCurrentName
>     r <- getDevNSupply
>     return (prefix ++ show (foldMap snd m + snd r))
> pickName _ s   = return s


The |piBoy| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piBoy :: (String :<: INTM) -> ProofState REF
> piBoy (s :<: ty) = checkHere (SET :>: ty) >>= piBoy' . (s :<:)

> piBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> piBoy' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> freshRef (s :<: tv) (\ref -> do
>             putEntryAbove (EPARAM ref (mkLastName ref) ParamPi ty)
>             return ref
>           )
>         Unknown _  -> throwError' $ err "piBoy: goal is not of type SET."
>         _          -> throwError' $ err "piBoy: only possible for incomplete goals."

The |select| command takes a term representing a neutral parameter, makes a new
goal of the same type, and fills it in with the parameter.

> select :: INTM -> ProofState (EXTM :=>: VAL)
> select tm@(N (P (name := k :<: ty))) = do
>     ty' <- bquoteHere ty
>     make (fst (last name) :<: ty')
>     goIn
>     give tm
> select _ = throwError' $ err "select: term is not a parameter."
     
The |ungawa| command looks for a truly obvious thing to do, and does it.

> ignore :: ProofState a -> ProofState ()
> ignore f = do
>     f
>     return ()

> ungawa :: ProofState ()
> ungawa = (ignore done <|> ignore apply <|> ignore (lambdaBoy "ug"))
>     `pushError` (err "ungawa: no can do.")



\subsection{Information Commands}

> infoAuncles :: ProofState String
> infoAuncles = do
>     pc <- get
>     inScope <- getInScope
>     return (showEntries (inBScope pc) inScope)

> infoDump :: ProofState String
> infoDump = gets show


The |getFakeMother| command returns a neutral application of a fake reference
that represents the mother of the current location. Note that its type is
$\lambda$-lifted over its great uncles, but it is then applied to them (as
shared parameters).

> getFakeRef :: ProofState REF
> getFakeRef = do
>    CDefinition _  (mnom := HOLE _ :<: ty) _ _ <- getCurrentEntry
>    return (mnom := FAKE :<: ty)

> getFakeMother :: ProofState (EXTM :=>: VAL)
> getFakeMother = do
>    r <- getFakeRef
>    inScope <- getInScope
>    let tm = P r $:$ (paramSpine inScope)
>    return $ tm :=>: evTm tm





When the current location or one of its children has suspended, we need to
update the outer layers.

> grandmotherSuspend :: SuspendState -> ProofState ()
> grandmotherSuspend ss = getLayers >>= putLayers . help ss
>   where
>     help :: SuspendState -> Bwd Layer -> Bwd Layer
>     help ss B0 = B0
>     help ss (ls :< l) = help ss' ls :< l{laySuspendState = ss'}
>       where ss' = min ss (laySuspendState l)