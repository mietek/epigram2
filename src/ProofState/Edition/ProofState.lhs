\section{The |ProofState| monad}
\label{sec:proof_state_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.ProofState where

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

> import ProofState.Structure.Developments
> import ProofState.Edition.News
> import ProofState.Edition.ProofContext

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

> mapStackError :: (ErrorTok a -> ErrorTok b) -> StackError a -> StackError b
> mapStackError = fmap . fmap

> liftError :: (a -> b) -> Either (StackError a) c -> Either (StackError b) c
> liftError f = either (Left . mapStackError (fmap f)) Right

> liftError' :: (ErrorTok a -> ErrorTok b) -> Either (StackError a) c
>     -> Either (StackError b) c
> liftError' f = either (Left . mapStackError f) Right

> liftErrorState :: (a -> b) -> ProofStateT a c -> ProofStateT b c
> liftErrorState f = mapStateT (liftError f)



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
> aunclesToElims F0                        = []
> aunclesToElims (EPARAM ref _ _ _ :> es)  = (A (N (P ref))) : aunclesToElims es
> aunclesToElims (_ :> es)                 = aunclesToElims es

