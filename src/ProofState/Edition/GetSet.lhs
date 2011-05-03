\section{The Get Set}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.GetSet where

> import Control.Monad.State
> import Data.Foldable

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.NatFinVec

> import DisplayLang.Scheme

> import ProofState.Structure.Developments

> import ProofState.Edition.News
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.Scope

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.ErrorHandling

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

> getLayers :: ProofState (Bwd Layer)
> getLayers = gets pcLayers
>
> getAboveCursor :: ProofState (Dev Bwd)
> getAboveCursor = gets pcAboveCursor
>
> getBelowCursor :: ProofState (Fwd (Entry Bwd))
> getBelowCursor = gets pcBelowCursor

And some specialized versions:

> getLayer :: ProofState Layer
> getLayer = do
>     _ :< l <- getLayers
>     return l


\subsubsection{Getting in |AboveCursor|}

> getEntriesAbove :: ProofState Entries
> getEntriesAbove = do
>     dev <- getAboveCursor
>     return $ devEntries dev
>
> getDevNSupply :: ProofState NameSupply
> getDevNSupply = do
>     dev <- getAboveCursor
>     return $ devNSupply dev
>
> getDevLev :: ProofState Int
> getDevLev = do
>     dev <- getAboveCursor
>     return $ devLevelCount dev
>
> getDevTip :: ProofState Tip
> getDevTip = do
>     dev <- getAboveCursor
>     return $ devTip dev

And some specialized versions:

> getEntryAbove :: ProofState (Entry Bwd)
> getEntryAbove = do
>     _ :< e <- getEntriesAbove
>     return e
>
> getGoal :: String -> ProofState TY
> getGoal s = do
>     tip <- getDevTip
>     case tip of
>       Unknown ty          -> return ty
>       Defined (ty :>: _)  -> return ty
>       _ -> throwError'  $ err "getGoal: fail to match a goal in " 
>                         ++ err s
>
> withGoal :: (TY -> ProofState ()) -> ProofState ()
> withGoal f = getGoal "withGoal" >>= f

\subsubsection{Getting in the |Layers|}

> getCurrentEntry :: ProofState CurrentEntry
> getCurrentEntry = do
>     ls <- getLayers
>     case ls of
>         _ :< l  -> return (currentEntry l)
>         B0      -> return (CModule []) 

\subsubsection{Getting in the |CurrentEntry|}

> getCurrentName :: ProofState Name
> getCurrentName = do
>     cEntry <-  getCurrentEntry
>     case cEntry of
>       CModule [] -> return []
>       _ -> return $ currentEntryName cEntry
>
> {-

> getCurrentDefinition :: ProofState EXP
> getCurrentDefinition = do
>     CDefinition d <- getCurrentEntry
>     scope <- getGlobalScope
>     return $ D d S0 (defOp d) $$$. scope

> -}

\paragraph{Getting in the |HOLE|\\}

> getHoleGoal :: ProofState TY
> getHoleGoal= do
>     tip <- getDevTip
>     case tip of
>       Unknown ty  -> return ty
>       _           -> throwError' $ err "getHoleGoal: goal is not a hole"

> {-

> getHoleGoal :: ProofState (INTM :=>: TY)
> getHoleGoal = do
>     CDefinition _ (_ := HOLE _ :<: _) _ _ _ <- getCurrentEntry
>     getGoal "getHoleGoal"
>
> getHoleKind :: ProofState HKind
> getHoleKind = do
>     CDefinition _ (_ := HOLE hk :<: _) _ _ _ <- getCurrentEntry
>     return hk

> -}


\subsubsection{Getting the Scopes}

> getInScope :: ProofState Entries
> getInScope = gets inScope

> {-
> getDefinitionsToImpl :: ProofState [REF :<: INTM]
> getDefinitionsToImpl = gets definitionsToImpl
> -}

> getGlobalScope :: ProofState Entries
> getGlobalScope = gets globalScope
>

> getParamsInScope :: ProofState [(ParamKind, String, TY)]
> getParamsInScope = do  
>     inScope <- getInScope
>     return $ params inScope

> getDefsInScope :: ProofState [DEF]
> getDefsInScope = do  
>     inScope <- getInScope
>     return $ foldMap def inScope
>   where
>     def (EDef def _)  = [def]
>     def _             = []


\subsection{Putters}


\subsubsection{Putting in |ProofContext|}

> putLayers :: Bwd Layer -> ProofState ()
> putLayers ls = do
>     pc <- get
>     put pc{pcLayers=ls}
>
> putAboveCursor :: Dev Bwd -> ProofState ()
> putAboveCursor dev = do
>     replaceAboveCursor dev
>     return ()

> putBelowCursor :: Fwd (Entry Bwd) -> ProofState (Fwd (Entry Bwd))
> putBelowCursor below = do
>     pc <- get
>     put pc{pcBelowCursor=below}
>     return (pcBelowCursor pc)

And some specialized versions:

> putLayer :: Layer -> ProofState ()
> putLayer l = do
>     pc@PC{pcLayers=ls} <- get
>     put pc{pcLayers=ls :< l}
>
> putEntryBelowCursor :: Entry Bwd -> ProofState ()
> putEntryBelowCursor e = do
>     below <- getBelowCursor
>     putBelowCursor (e :> below)
>     return ()

> putDevLev :: Int -> ProofState ()
> putDevLev l = do
>     dev <- getAboveCursor
>     putAboveCursor (dev{devLevelCount=l})



\subsubsection{Putting in |AboveCursor|}

> putEntriesAbove :: Entries -> ProofState ()
> putEntriesAbove es = do
>     replaceEntriesAbove es
>     return ()
>
> putDevNSupply :: NameSupply -> ProofState ()
> putDevNSupply ns = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devNSupply = ns}
>
> putDevSuspendState :: SuspendState -> ProofState ()
> putDevSuspendState ss = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devSuspendState = ss}
>
> putDevTip :: Tip -> ProofState ()
> putDevTip tip = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devTip = tip}

And some specialized versions:

> putEntryAbove :: Entry Bwd -> ProofState ()
> putEntryAbove e = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devEntries = devEntries dev :< e}

\subsubsection{Putting in the |Layers|}

> putCurrentEntry :: CurrentEntry -> ProofState ()
> putCurrentEntry m = do
>     l <- getLayer
>     _ <- replaceLayer l{currentEntry=m}
>     return ()
>
> putNewsBelow :: NewsBulletin -> ProofState ()
> putNewsBelow news = do
>     l <- getLayer
>     replaceLayer l{belowEntries = NF (Left news :> unNF (belowEntries l))}
>     return ()


\subsubsection{Putting in the |CurrentEntry|}

\paragraph{Putting in the |PROG|\\}

> {-

> putCurrentScheme :: Scheme INTM -> ProofState ()
> putCurrentScheme sch = do
>     CDefinition _ ref xn ty a <- getCurrentEntry
>     putCurrentEntry $ CDefinition (PROG sch) ref xn ty a

\paragraph{Putting in the |HOLE|\\}



> putHoleKind :: HKind -> ProofState ()
> putHoleKind hk = do
>     CDefinition kind (name := HOLE _ :<: ty) xn tm a <- getCurrentEntry
>     putCurrentEntry $ CDefinition kind (name := HOLE hk :<: ty) xn tm a

> -}

\subsection{Removers}

\subsubsection{Remove in |ProofContext|}

> removeLayer :: ProofState Layer
> removeLayer = do
>     pc@PC{pcLayers=ls :< l} <- get
>     put pc{pcLayers=ls}
>     return l

\subsubsection{Removing in |AboveEntries|}

> removeEntryAbove :: ProofState (Maybe (Entry Bwd))
> removeEntryAbove = do
>     es <- getEntriesAbove
>     case es of
>       B0 -> return Nothing
>       (es' :< e) -> do
>         putEntriesAbove es'
>         return $ Just e


\subsection{Replacers}

\subsubsection{Replacing into |ProofContext|}

> replaceAboveCursor :: Dev Bwd -> ProofState (Dev Bwd)
> replaceAboveCursor dev = do
>     pc <- get
>     put pc{pcAboveCursor=dev}
>     return (pcAboveCursor pc)

And some specialized version:

> replaceLayer :: Layer -> ProofState Layer
> replaceLayer l = do
>     (ls :< l') <- getLayers
>     putLayers (ls :< l)
>     return l'

\subsubsection{Replacing in |AboveCursor|}

> replaceEntriesAbove :: Entries -> ProofState Entries
> replaceEntriesAbove es = do
>     dev <- getAboveCursor
>     putAboveCursor dev{devEntries = es}
>     return (devEntries dev)





> getBoyCount :: ProofState Int
> getBoyCount = do
>     inScope <- getInScope
>     return $ Data.Foldable.foldr countParam 0 inScope
>   where
>     countParam (EParam _ _ _ _) n = 1 + n
>     countParam _                n = n


The |updateDefFromTip| command updates the current entry (which must
be a definition) after its tip has been updated. It lambda-lifts the
tip type (and term, if there is one) to produce an updated |DEF|,
which it stores as the current entry. It returns the updated |DEF|
along with the result of applying it to the spine of shared
parameters.

This is used by |give| and |make|, plus the news propagation
machinery. Perhaps it should move somewhere more logical.

> updateDefFromTip :: ProofState (DEF, EXP)
> updateDefFromTip = do
>     tip <- getDevTip
>     nom <- getCurrentName
>     let ty = case tip of
>                  Unknown t          -> t
>                  Defined (t :>: _)  -> t
>     inScope <- getInScope
>     let  binScope = boys inScope
>          ty' = bwdVec (fmap (\(_, s, t) -> (s, t)) binScope)
>                           (\ n ys -> piLift n ys) ty
>          lev = Data.Foldable.foldr (\_ -> (1+)) 0 binScope
>          op = eats lev (tipToOp tip)
>          def' = DEF nom ty' op
>     putCurrentEntry $ CDefinition def'
>     return (def', D def' S0 op $$$ fmap (\x -> A (P x :$ B0)) binScope)
>  where 
>    boys :: Entries -> Bwd (Int, String, TY)
>    boys B0 = B0
>    boys (es :< EParam _ s t l) =  boys es :< (l, s, t)
>    boys (es :< _) =  boys es 

>    tipToOp (Unknown _)           = Hole
>    tipToOp (Defined (_ :>: tm))  = Emit tm