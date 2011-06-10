\section{The |ProofState| monad}
\label{sec:ProofState.Edition.ProofState}

Move to |ProofState.ProofContext|?

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.ProofState where

> import Control.Monad.State

> import DisplayLang.Name

> import ProofState.Edition.ProofContext

> import Evidences.Tm
> import Evidences.ErrorHandling

%endif


\subsection{Defining the Proof State monad}


The proof state monad provides access to the |ProofContext| as in a
|State| monad, but with the possibility of command failure represented
by |Either StackError|. 

> type ProofState = StateT ProofContext (Either StackError)

Most of the time, we will work in a |ProofStateT| carrying errors
composed with Strings and terms in display syntax. Hence the following
type synonym:



