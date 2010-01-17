\section{The |ProofState| monad}
\label{sec:proof_state_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.ProofState where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.Foldable
> import Debug.Trace

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import DisplayLang.DisplayTm

> import ProofState.Developments
> import ProofState.News
> import ProofState.ProofContext

> import Evidences.Tm

%endif


\subsection{Defining the Proof State monad}


The proof state monad provides access to the |ProofContext| as in a
|State| monad, but with the possibility of command failure represented
by |Either StackError|.

> type ProofState = StateT ProofContext (Either StackError)


\subsection{Getters and Setters}

We provide various functions to get information from the proof state and store
updated information, providing a friendlier interface than |get| and |put|.

\question{That would be great to have an illustration of the behavior
          of each of these functions on a development.}

\subsubsection{Getters}

> getAuncles :: ProofState (Entries)
> getAuncles = get >>= return . auncles

> getDev :: ProofState (Dev Bwd)
> getDev = gets snd

> getDevEntries :: ProofState (Entries)
> getDevEntries = do
>     (es, _, _) <- getDev
>     return es

> getDevEntry :: ProofState (Entry Bwd)
> getDevEntry = do
>     (_ :< e, _, _) <- getDev
>     return e

> getDevNSupply :: ProofState NameSupply
> getDevNSupply = do
>     (_, _, ns) <- getDev
>     return ns

> getDevTip :: ProofState Tip
> getDevTip = do
>     (_, tip, _) <- getDev
>     return tip

> getGoal :: String -> ProofState (INTM :=>: TY)
> getGoal s = do
>     tip <- getDevTip
>     case tip of
>       Unknown (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       Defined _ (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       _ -> throwError' $ "getGoal: fail to match a goal in " ++ s

> getGreatAuncles :: ProofState Entries
> getGreatAuncles = get >>= return . greatAuncles

> getBoys = do  
>     auncles <- getAuncles
>     return $ foldMap boy auncles 
>    where boy (E r _ (Boy _) _)  = [r]
>          boy _ = []

> getHoleGoal :: ProofState (INTM :=>: TY)
> getHoleGoal = do
>     GirlMother (_ := HOLE :<: _) _ _ <- getMother
>     getGoal "getHoleGoal"

> getLayer :: ProofState Layer
> getLayer = do
>     ls :< l <- getLayers
>     return l

> getLayers :: ProofState (Bwd Layer)
> getLayers = gets fst

> getMother :: ProofState Mother
> getMother = do
>     ls <- getLayers
>     case ls of
>         _ :< l  -> return (mother l)
>         B0      -> return (ModuleMother []) 

> getMotherEntry :: ProofState (Entry Bwd)
> getMotherEntry = do
>     m <- getMother
>     dev <- getDev
>     case m of
>         GirlMother ref xn ty -> return (E ref xn (Girl LETG dev) ty)
>         ModuleMother n -> return (M n dev)

> getMotherName :: ProofState Name
> getMotherName = do
>     ls <- gets fst
>     case ls of
>         (_ :< Layer{mother=m}) -> return (motherName m)
>         B0 -> return []


\subsubsection{Putters}


> insertCadet :: NewsBulletin -> ProofState ()
> insertCadet news = do
>     l <- getLayer
>     replaceLayer l{cadets = NF (Left news :> unNF (cadets l))}
>     return ()

> putDev :: Dev Bwd -> ProofState ()
> putDev dev = do
>     ls <- gets fst
>     put (ls, dev)

> putDevEntry :: Entry Bwd -> ProofState ()
> putDevEntry e = do
>     (es, tip, nsupply) <- getDev
>     putDev (es :< e, tip, nsupply)

> putDevEntries :: Entries -> ProofState ()
> putDevEntries es = do
>     (_, tip, nsupply) <- getDev
>     putDev (es, tip, nsupply)

> putDevNSupply :: NameSupply -> ProofState ()
> putDevNSupply ns = do
>     (es, tip, _) <- getDev
>     putDev (es, tip, ns)

> putDevTip :: Tip -> ProofState ()
> putDevTip tip = do
>     (es, _, r) <- getDev
>     putDev (es, tip, r)

> putLayer :: Layer -> ProofState ()
> putLayer l = do
>     (ls, dev) <- get
>     put (ls :< l, dev)

> putMother :: Mother -> ProofState ()
> putMother m = do
>     l <- getLayer
>     _ <- replaceLayer l{mother=m}
>     return ()

> putMotherEntry :: Entry Bwd -> ProofState ()
> putMotherEntry (E ref xn (Girl LETG dev) ty) = do
>     l <- getLayer
>     replaceLayer (l{mother=GirlMother ref xn ty})
>     putDev dev
> putMotherEntry (M [] dev) = putDev dev
> putMotherEntry (M n dev) = do
>     l <- getLayer
>     replaceLayer (l{mother=ModuleMother n})
>     putDev dev


\subsubsection{Removers}


> removeDevEntry :: ProofState (Maybe (Entry Bwd))
> removeDevEntry = do
>     es <- getDevEntries
>     case es of
>       B0 -> return Nothing
>       (es' :< e) -> do
>         putDevEntries es'
>         return (Just e)

> removeLayer :: ProofState Layer
> removeLayer = do
>     (ls :< l, dev) <- get
>     put (ls, dev)
>     return l

\subsubsection{Replacers}

> replaceDev :: Dev Bwd -> ProofState (Dev Bwd)
> replaceDev dev = do
>     (ls, dev') <- get
>     put (ls, dev)
>     return dev'

> replaceDevEntries :: Entries -> ProofState Entries
> replaceDevEntries es = do
>     es' <- getDevEntries
>     putDevEntries es
>     return es'

> replaceLayer :: Layer -> ProofState Layer
> replaceLayer l = do
>     (ls :< l', dev) <- get
>     put (ls :< l, dev)
>     return l'

\subsubsection{Tracing in the |ProofState| monad}

> proofTrace :: String -> ProofState ()
> proofTrace s = do
>   () <- trace s $ return ()
>   return ()
