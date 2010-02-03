\section{The |ProofState| monad}
\label{sec:proof_state_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.ProofState where

> import Control.Monad.State
> import Data.Foldable
> import Debug.Trace

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> -- XXX: bug "fix" of the dependency graph:
> import DisplayLang.DisplayTm 
> import DisplayLang.Naming

> import ProofState.Developments
> import ProofState.News
> import ProofState.ProofContext

> import Evidences.Rules
> import Evidences.Tm

%endif


\subsection{Defining the Proof State monad}


The proof state monad provides access to the |ProofContext| as in a
|State| monad, but with the possibility of command failure represented
by |Either (StackError e)|. 

> type ProofStateT e = StateT ProofContext (Either (StackError e))

Most of the time, we will work in a |ProofStateT| carrying errors
composed with Strings and terms in display syntax. Hence the following
type synonym:

> type ProofState = ProofStateT InDTmRN


\subsection{Getters and Setters}

We provide various functions to get information from the proof state and store
updated information, providing a friendlier interface than |get| and |put|.

\question{That would be great to have an illustration of the behavior
          of each of these functions on a development.}

\subsubsection{Getters}

> getAuncles :: ProofStateT e (Entries)
> getAuncles = get >>= return . auncles

> getDev :: ProofStateT e (Dev Bwd)
> getDev = gets snd

> getDevEntries :: ProofStateT e (Entries)
> getDevEntries = do
>     (es, _, _) <- getDev
>     return es

> getDevEntry :: ProofStateT e (Entry Bwd)
> getDevEntry = do
>     (_ :< e, _, _) <- getDev
>     return e

> getDevNSupply :: ProofStateT e NameSupply
> getDevNSupply = do
>     (_, _, ns) <- getDev
>     return ns

> getDevTip :: ProofStateT e Tip
> getDevTip = do
>     (_, tip, _) <- getDev
>     return tip

> getGoal :: String -> ProofStateT e (INTM :=>: TY)
> getGoal s = do
>     tip <- getDevTip
>     case tip of
>       Unknown (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       Defined _ (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       _ -> throwError'  $ err "getGoal: fail to match a goal in " 
>                         ++ err s

> getGreatAuncles :: ProofStateT e Entries
> getGreatAuncles = get >>= return . greatAuncles

> getBoys :: ProofStateT e [REF]
> getBoys = do  
>     auncles <- getAuncles
>     return $ foldMap boy auncles 
>    where boy (E r _ (Boy _) _)  = [r]
>          boy _ = []

> getHoleGoal :: ProofStateT e (INTM :=>: TY)
> getHoleGoal = do
>     GirlMother (_ := HOLE _ :<: _) _ _ _ <- getMother
>     getGoal "getHoleGoal"

> getLayer :: ProofStateT e Layer
> getLayer = do
>     ls :< l <- getLayers
>     return l

> getLayers :: ProofStateT e (Bwd Layer)
> getLayers = gets fst

> getMother :: ProofStateT e Mother
> getMother = do
>     ls <- getLayers
>     case ls of
>         _ :< l  -> return (mother l)
>         B0      -> return (ModuleMother []) 

> getMotherDefinition :: ProofStateT e (EXTM :=>: VAL)
> getMotherDefinition = do
>     GirlMother ref _ _ _ <- getMother
>     aus <- getGreatAuncles
>     return (applyAuncles ref aus)

> getMotherEntry :: ProofStateT e (Entry Bwd)
> getMotherEntry = do
>     m <- getMother
>     dev <- getDev
>     case m of
>         GirlMother ref xn ty ms -> return (E ref xn (Girl LETG dev ms) ty)
>         ModuleMother n -> return (M n dev)

> getMotherName :: ProofStateT e Name
> getMotherName = do
>     ls <- gets fst
>     case ls of
>         (_ :< Layer{mother=m}) -> return (motherName m)
>         B0 -> return []


\subsubsection{Putters}


> insertCadet :: NewsBulletin -> ProofStateT e ()
> insertCadet news = do
>     l <- getLayer
>     replaceLayer l{cadets = NF (Left news :> unNF (cadets l))}
>     return ()

> putDev :: Dev Bwd -> ProofStateT e ()
> putDev dev = do
>     ls <- gets fst
>     put (ls, dev)

> putDevEntry :: Entry Bwd -> ProofStateT e ()
> putDevEntry e = do
>     (es, tip, nsupply) <- getDev
>     putDev (es :< e, tip, nsupply)

> putDevEntries :: Entries -> ProofStateT e ()
> putDevEntries es = do
>     (_, tip, nsupply) <- getDev
>     putDev (es, tip, nsupply)

> putDevNSupply :: NameSupply -> ProofStateT e ()
> putDevNSupply ns = do
>     (es, tip, _) <- getDev
>     putDev (es, tip, ns)

> putDevTip :: Tip -> ProofStateT e ()
> putDevTip tip = do
>     (es, _, r) <- getDev
>     putDev (es, tip, r)

> putLayer :: Layer -> ProofStateT e ()
> putLayer l = do
>     (ls, dev) <- get
>     put (ls :< l, dev)

> putMother :: Mother -> ProofStateT e ()
> putMother m = do
>     l <- getLayer
>     _ <- replaceLayer l{mother=m}
>     return ()

> putMotherEntry :: Entry Bwd -> ProofStateT e ()
> putMotherEntry (E ref xn (Girl LETG dev ms) ty) = do
>     l <- getLayer
>     replaceLayer (l{mother=GirlMother ref xn ty ms})
>     putDev dev
> putMotherEntry (M [] dev) = putDev dev
> putMotherEntry (M n dev) = do
>     l <- getLayer
>     replaceLayer (l{mother=ModuleMother n})
>     putDev dev

> putMotherScheme :: Scheme INTM -> ProofState ()
> putMotherScheme sch = do
>     GirlMother ref xn ty _ <- getMother
>     putMother (GirlMother ref xn ty (Just sch))

\subsubsection{Removers}


> removeDevEntry :: ProofStateT e (Maybe (Entry Bwd))
> removeDevEntry = do
>     es <- getDevEntries
>     case es of
>       B0 -> return Nothing
>       (es' :< e) -> do
>         putDevEntries es'
>         return (Just e)

> removeLayer :: ProofStateT e Layer
> removeLayer = do
>     (ls :< l, dev) <- get
>     put (ls, dev)
>     return l

\subsubsection{Replacers}

> replaceDev :: Dev Bwd -> ProofStateT e (Dev Bwd)
> replaceDev dev = do
>     (ls, dev') <- get
>     put (ls, dev)
>     return dev'

> replaceDevEntries :: Entries -> ProofStateT e Entries
> replaceDevEntries es = do
>     es' <- getDevEntries
>     putDevEntries es
>     return es'

> replaceLayer :: Layer -> ProofStateT e Layer
> replaceLayer l = do
>     (ls :< l', dev) <- get
>     put (ls :< l, dev)
>     return l'

\subsubsection{Tracing in the |ProofState| monad}

> proofTrace :: String -> ProofStateT e ()
> proofTrace s = do
>   () <- trace s $ return ()
>   return ()

\subsubsection{Useful odds and ends}

The |applyAuncles| command applies a reference to the given
spine of shared parameters.

> applyAuncles :: REF -> Entries -> EXTM :=>: VAL
> applyAuncles ref aus = tm :=>: evTm tm
>   where tm = P ref $:$ aunclesToElims (aus <>> F0)

> aunclesToElims :: Fwd (Entry Bwd) -> [Elim INTM]
> aunclesToElims F0 = []
> aunclesToElims (E ref _ (Boy _) _ :> es) = (A (N (P ref))) : aunclesToElims es
> aunclesToElims (_ :> es) = aunclesToElims es