\section{The Get Set}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.GetSet where

> import Control.Monad.State

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import DisplayLang.Scheme

> import ProofState.Structure.Developments

> import ProofState.Edition.News
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.Scope

> import Evidences.Tm

%endif

We provide various functions to get information from the proof state
and store updated information, providing a friendlier interface than
|get| and |put|. The rule of thumb for naming these functions is to
prefix the name of a field by the action (|get|, |put|, |remove|, or
|replace|).

\question{That would be great to have an illustration of the behavior
          of each of these functions on a development.}

\pierre{Some of these functions pattern-match aggressively, at the
risk of failing. Others carefully wrap their results in a |Maybe|. It
would be good to decide a uniform approach there.}


\subsection{Getters}


\subsubsection{Getting in |ProofContext|}

> getLayers :: ProofStateT e (Bwd Layer)
> getLayers = gets pcLayers
>
> getAboveCursor :: ProofStateT e (Dev Bwd)
> getAboveCursor = gets pcAboveCursor
>
> getBelowCursor :: ProofStateT e (Fwd (Entry Bwd))
> getBelowCursor = gets pcBelowCursor

And some specialized versions:

> getLayer :: ProofStateT e Layer
> getLayer = do
>     _ :< l <- getLayers
>     return l


\subsubsection{Getting in |AboveCursor|}

> getEntriesAbove :: ProofStateT e Entries
> getEntriesAbove = do
>     dev <- getAboveCursor
>     return $ devEntries dev
>
> getDevNSupply :: ProofStateT e NameSupply
> getDevNSupply = do
>     dev <- getAboveCursor
>     return $ devNSupply dev
>
> getDevTip :: ProofStateT e Tip
> getDevTip = do
>     dev <- getAboveCursor
>     return $ devTip dev

And some specialized versions:

> getEntryAbove :: ProofStateT e (Entry Bwd)
> getEntryAbove = do
>     _ :< e <- getEntriesAbove
>     return e
>
> getGoal :: String -> ProofStateT e (INTM :=>: TY)
> getGoal s = do
>     tip <- getDevTip
>     case tip of
>       Unknown (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       Defined _ (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       _ -> throwError'  $ err "getGoal: fail to match a goal in " 
>                         ++ err s
>
> withGoal :: (VAL -> ProofState ()) -> ProofState ()
> withGoal f = do
>   (_ :=>: goal) <- getGoal "withGoal"
>   f goal

\subsubsection{Getting in the |Layers|}

> getCurrentEntry :: ProofStateT e CurrentEntry
> getCurrentEntry = do
>     ls <- getLayers
>     case ls of
>         _ :< l  -> return (currentEntry l)
>         B0      -> return (CModule []) 

\subsubsection{Getting in the |CurrentEntry|}

> getCurrentName :: ProofStateT e Name
> getCurrentName = do
>     cEntry <-  getCurrentEntry
>     case cEntry of
>       CModule [] -> return []
>       _ -> return $ currentEntryName cEntry
>
> getCurrentDefinition :: ProofStateT e (EXTM :=>: VAL)
> getCurrentDefinition = do
>     CDefinition _ ref _ _ _ <- getCurrentEntry
>     scope <- getGlobalScope
>     return (applySpine ref scope)

\paragraph{Getting in the |HOLE|\\}

> getHoleGoal :: ProofStateT e (INTM :=>: TY)
> getHoleGoal = do
>     CDefinition _ (_ := HOLE _ :<: _) _ _ _ <- getCurrentEntry
>     getGoal "getHoleGoal"
>
> getHoleKind :: ProofStateT e HKind
> getHoleKind = do
>     CDefinition _ (_ := HOLE hk :<: _) _ _ _ <- getCurrentEntry
>     return hk



\subsubsection{Getting the Scopes}

> getInScope :: ProofStateT e Entries
> getInScope = gets inScope
>
> getDefinitionsToImpl :: ProofStateT e [REF :<: INTM]
> getDefinitionsToImpl = gets definitionsToImpl
>
> getGlobalScope :: ProofStateT e Entries
> getGlobalScope = gets globalScope
>
> getParamsInScope :: ProofStateT e [REF]
> getParamsInScope = do  
>     inScope <- getInScope
>     return $ paramREFs inScope


\subsection{Putters}


\subsubsection{Putting in |ProofContext|}

> putLayers :: Bwd Layer -> ProofStateT e ()
> putLayers ls = do
>     pc <- get
>     put pc{pcLayers=ls}
>
> putAboveCursor :: Dev Bwd -> ProofStateT e ()
> putAboveCursor dev = do
>     replaceAboveCursor dev
>     return ()

> putBelowCursor :: Fwd (Entry Bwd) -> ProofStateT e (Fwd (Entry Bwd))
> putBelowCursor below = do
>     pc <- get
>     put pc{pcBelowCursor=below}
>     return (pcBelowCursor pc)

And some specialized versions:

> putLayer :: Layer -> ProofStateT e ()
> putLayer l = do
>     pc@PC{pcLayers=ls} <- get
>     put pc{pcLayers=ls :< l}
>
> putEntryBelowCursor :: Entry Bwd -> ProofStateT e ()
> putEntryBelowCursor e = do
>     below <- getBelowCursor
>     putBelowCursor (e :> below)
>     return ()



\subsubsection{Putting in |AboveCursor|}

> putEntriesAbove :: Entries -> ProofStateT e ()
> putEntriesAbove es = do
>     replaceEntriesAbove es
>     return ()
>
> putDevNSupply :: NameSupply -> ProofStateT e ()
> putDevNSupply ns = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devNSupply = ns}
>
> putDevSuspendState :: SuspendState -> ProofStateT e ()
> putDevSuspendState ss = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devSuspendState = ss}
>
> putDevTip :: Tip -> ProofStateT e ()
> putDevTip tip = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devTip = tip}

And some specialized versions:

> putEntryAbove :: Entry Bwd -> ProofStateT e ()
> putEntryAbove e = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devEntries = devEntries dev :< e}

\subsubsection{Putting in the |Layers|}

> putCurrentEntry :: CurrentEntry -> ProofStateT e ()
> putCurrentEntry m = do
>     l <- getLayer
>     _ <- replaceLayer l{currentEntry=m}
>     return ()
>
> putNewsBelow :: NewsBulletin -> ProofStateT e ()
> putNewsBelow news = do
>     l <- getLayer
>     replaceLayer l{belowEntries = NF (Left news :> unNF (belowEntries l))}
>     return ()


\subsubsection{Putting in the |CurrentEntry|}

\paragraph{Putting in the |PROG|\\}

> putCurrentScheme :: Scheme INTM -> ProofState ()
> putCurrentScheme sch = do
>     CDefinition _ ref xn ty a <- getCurrentEntry
>     putCurrentEntry $ CDefinition (PROG sch) ref xn ty a

\paragraph{Putting in the |HOLE|\\}

> putHoleKind :: HKind -> ProofStateT e ()
> putHoleKind hk = do
>     CDefinition kind (name := HOLE _ :<: ty) xn tm a <- getCurrentEntry
>     putCurrentEntry $ CDefinition kind (name := HOLE hk :<: ty) xn tm a


\subsection{Removers}

\subsubsection{Remove in |ProofContext|}

> removeLayer :: ProofStateT e Layer
> removeLayer = do
>     pc@PC{pcLayers=ls :< l} <- get
>     put pc{pcLayers=ls}
>     return l

\subsubsection{Removing in |AboveEntries|}

> removeEntryAbove :: ProofStateT e (Maybe (Entry Bwd))
> removeEntryAbove = do
>     es <- getEntriesAbove
>     case es of
>       B0 -> return Nothing
>       (es' :< e) -> do
>         putEntriesAbove es'
>         return $ Just e


\subsection{Replacers}

\subsubsection{Replacing into |ProofContext|}

> replaceAboveCursor :: Dev Bwd -> ProofStateT e (Dev Bwd)
> replaceAboveCursor dev = do
>     pc <- get
>     put pc{pcAboveCursor=dev}
>     return (pcAboveCursor pc)

And some specialized version:

> replaceLayer :: Layer -> ProofStateT e Layer
> replaceLayer l = do
>     (ls :< l') <- getLayers
>     putLayers (ls :< l)
>     return l'

\subsubsection{Replacing in |AboveCursor|}

> replaceEntriesAbove :: Entries -> ProofStateT e Entries
> replaceEntriesAbove es = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devEntries = es}
>     return (devEntries dev)



