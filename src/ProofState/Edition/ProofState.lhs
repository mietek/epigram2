\section{The |ProofState| monad}
\label{sec:ProofState.Edition.ProofState}

Move to |ProofState.ProofContext|?

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, GeneralizedNewtypeDeriving #-}

> module ProofState.Edition.ProofState where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State

> import ProofState.Edition.ProofContext

> import Evidences.ErrorHandling

%endif


\subsection{Defining the Proof State monad}


The proof state monad provides access to the |ProofContext| as in a
|State| monad, but with the possibility of command failure represented
by |Either StackError|. 

> newtype ProofState a = ProofState
>     {unProofState :: StateT ProofContext (Either StackError) a}
>   deriving  (  Applicative
>             ,  Alternative
>             ,  Functor
>             ,  MonadError StackError
>             ,  MonadPlus
>             ,  MonadState ProofContext
>             )

This is annoying. We need |ProofState| to be a newtype so that we can
override the |fail| behaviour of the |Monad| instance to invoke
|throwError| rather than crashing with |error|.

> instance Monad ProofState where
>     return              = ProofState . return
>     ProofState x >>= f  = ProofState (x >>= (unProofState . f))
>     fail s              = throwError [err s]


> evalProofState :: ProofState a -> ProofContext -> Either StackError a
> evalProofState  = evalStateT . unProofState

> runProofState :: ProofState a -> ProofContext -> Either StackError (a, ProofContext)
> runProofState   = runStateT . unProofState

> execProofState :: ProofState a -> ProofContext -> Either StackError ProofContext
> execProofState  = execStateT . unProofState