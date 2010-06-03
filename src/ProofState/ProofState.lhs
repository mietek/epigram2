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
> import DisplayLang.Scheme
> import DisplayLang.Name

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

> type ProofState = ProofStateT DInTmRN


Some functions, such as |distill|, are defined in the |ProofStateT
INTM| monad. However, Cochon lives in a |ProofStateT DInTmRN|
monad. Therefore, in order to use it, we will need to lift from the
former to the latter.

> liftError :: Either (StackError INTM) a -> Either (StackError InDTmRN) a
> liftError = either (Left . wrapError) Right
>     where wrapError :: StackError INTM -> StackError InDTmRN
>           wrapError = fmap $           -- on the stack
>                       fmap $           -- on the list of token
>                       fmap             -- on a token
>                       (DT . InTmWrap)  -- turning INTM into InDTmRN



\subsection{Getters and Setters}

We provide various functions to get information from the proof state and store
updated information, providing a friendlier interface than |get| and |put|.

\question{That would be great to have an illustration of the behavior
          of each of these functions on a development.}

\subsubsection{Getters}

> getAuncles :: ProofStateT e Entries
> getAuncles = gets auncles

> getAunclesToImpl :: ProofStateT e [REF :<: INTM]
> getAunclesToImpl = gets aunclesToImpl

> getDev :: ProofStateT e (Dev Bwd)
> getDev = gets pcDev

> getDevCadets :: ProofStateT e (Fwd (Entry Bwd))
> getDevCadets = gets pcCadets

> getDevEntries :: ProofStateT e Entries
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
> getGreatAuncles = gets greatAuncles

> getBoys :: ProofStateT e [REF]
> getBoys = do  
>     auncles <- getAuncles
>     return $ foldMap boy auncles 
>    where boy (E r _ (Boy _) _)  = [r]
>          boy _ = []

> getBoysBwd :: ProofStateT e (Bwd REF)
> getBoysBwd = do  
>     auncles <- getAuncles
>     return $ foldMap boy auncles 
>    where boy (E r _ (Boy _) _)  = (B0 :< r)
>          boy _ = B0

> getHoleGoal :: ProofStateT e (INTM :=>: TY)
> getHoleGoal = do
>     GirlMother _ (_ := HOLE _ :<: _) _ _ <- getMother
>     getGoal "getHoleGoal"

> getHoleKind :: ProofStateT e HKind
> getHoleKind = do
>     GirlMother _ (_ := HOLE hk :<: _) _ _ <- getMother
>     return hk

> getLayer :: ProofStateT e Layer
> getLayer = do
>     ls :< l <- getLayers
>     return l

> getLayers :: ProofStateT e (Bwd Layer)
> getLayers = gets pcLayers

> getMother :: ProofStateT e Mother
> getMother = do
>     ls <- getLayers
>     case ls of
>         _ :< l  -> return (mother l)
>         B0      -> return (ModuleMother []) 

> getMotherDefinition :: ProofStateT e (EXTM :=>: VAL)
> getMotherDefinition = do
>     GirlMother _ ref _ _ <- getMother
>     aus <- getGreatAuncles
>     return (applyAuncles ref aus)

> getMotherEntry :: ProofStateT e (Entry Bwd)
> getMotherEntry = do
>     m <- getMother
>     (es, tip, root) <- getDev
>     cadets <- getDevCadets
>     let dev = (es <>< cadets, tip, root)
>     case m of
>         GirlMother kind ref xn ty -> return
>             (E ref xn (Girl kind dev) ty)
>         ModuleMother n -> return (M n dev)

> getMotherName :: ProofStateT e Name
> getMotherName = do
>     ls <- getLayers
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
>     pc <- get
>     put pc{pcDev=dev}

> putDevCadet :: Entry Bwd -> ProofStateT e ()
> putDevCadet e = do
>     cadets <- getDevCadets
>     putDevCadets (e :> cadets)
>     return ()

> putDevCadets :: Fwd (Entry Bwd) -> ProofStateT e (Fwd (Entry Bwd))
> putDevCadets cadets = do
>     pc <- get
>     put pc{pcCadets=cadets}
>     return (pcCadets pc)

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

> putHoleKind :: HKind -> ProofStateT e ()
> putHoleKind hk = do
>     GirlMother kind (name := HOLE _ :<: ty) xn tm <- getMother
>     putMother $ GirlMother kind (name := HOLE hk :<: ty) xn tm

> putLayer :: Layer -> ProofStateT e ()
> putLayer l = do
>     pc@PC{pcLayers=ls} <- get
>     put pc{pcLayers=ls :< l}

> putLayers :: Bwd Layer -> ProofStateT e ()
> putLayers ls = do
>     pc <- get
>     put pc{pcLayers=ls}

> putMother :: Mother -> ProofStateT e ()
> putMother m = do
>     l <- getLayer
>     _ <- replaceLayer l{mother=m}
>     return ()

> putMotherEntry :: Entry Bwd -> ProofStateT e ()
> putMotherEntry (E ref xn (Girl kind dev) ty) = do
>     l <- getLayer
>     replaceLayer (l{mother=GirlMother kind ref xn ty})
>     putDev dev
> putMotherEntry (M [] dev) = putDev dev
> putMotherEntry (M n dev) = do
>     l <- getLayer
>     replaceLayer (l{mother=ModuleMother n})
>     putDev dev

> putMotherScheme :: Scheme INTM -> ProofState ()
> putMotherScheme sch = do
>     GirlMother _ ref xn ty <- getMother
>     putMother (GirlMother (PROG sch) ref xn ty)

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
>     pc@PC{pcLayers=ls :< l} <- get
>     put pc{pcLayers=ls}
>     return l

\subsubsection{Replacers}

> replaceDev :: Dev Bwd -> ProofStateT e (Dev Bwd)
> replaceDev dev = do
>     pc <- get
>     put pc{pcDev=dev}
>     return (pcDev pc)

> replaceDevEntries :: Entries -> ProofStateT e Entries
> replaceDevEntries es = do
>     es' <- getDevEntries
>     putDevEntries es
>     return es'

> replaceLayer :: Layer -> ProofStateT e Layer
> replaceLayer l = do
>     (ls :< l') <- getLayers
>     putLayers (ls :< l)
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
