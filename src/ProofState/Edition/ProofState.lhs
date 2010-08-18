\section{The |ProofState| monad}
\label{sec:ProofState.Edition.ProofState}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.ProofState where

> import Control.Monad.State

> import DisplayLang.Name

> import ProofState.Edition.ProofContext

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


\subsection{Error management toolkit}

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
