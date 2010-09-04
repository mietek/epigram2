\section{The |ProofState| Kit}
\label{sec:ProofState.Interface.ProofKit}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.ProofKit where

> import Control.Monad.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Evidences.Tm
> import Evidences.TypeChecker
> import Evidences.BetaQuotation

%endif


The proof state lives on a rich substrate of operations, inherited
from the |ProofContext| as well as the |ProofState| monad. In this
module, we export these operations as part of the Interface.



\subsection{Accessing the |NameSupply|}


By definition of the |Development| in
Section~\ref{sec:ProofState.Structure.Developments}, we have that
every entry is associated a namespace by the mean of a local name
supply. As a result, the |ProofState| can almost be made a
|NameSupplier|. The exception being that it cannot fork the name
supply, because it cannot generates new namespaces.

> instance NameSupplier (ProofStateT e) where
>     freshRef (s :<: ty) f = do
>         nsupply <- getDevNSupply
>         freshRef (s :<: ty) ( \ref nsupply' -> do
>             putDevNSupply nsupply'
>             f ref
>           ) nsupply
>
>     forkNSupply = error "ProofState does not provide forkNSupply"
>     
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply to
proof state commands.

> withNSupply :: (NameSupply -> x) -> ProofStateT e x
> withNSupply f = getDevNSupply >>= return . f

\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


\subsection{Accessing the type-checker}


First off, we can access the $\beta$-normalizer: the |bquoteHere|
command $\beta$-quotes a term using the local name supply.

> bquoteHere :: Tm {d, VV} REF -> ProofStateT e (Tm {d, TT} REF)
> bquoteHere tm = withNSupply $ bquote B0 tm


Secondly, any type-checking problem (defined in the |Check| monad) can
be executed in the |ProofState|.

> runCheckHere :: (ErrorTok e -> ErrorTok DInTmRN) -> Check e a -> ProofState a
> runCheckHere f c = do
>     me <- withNSupply $ liftError' f . typeCheck c
>     lift me

As a consequence, we have |checkHere| to |check| terms against types:

> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere tt = runCheckHere (fmap DTIN) $ check tt

and |inferHere| to |infer| types from terms:

> inferHere :: EXTM -> ProofState (VAL :<: TY)
> inferHere tm = runCheckHere (fmap DTIN) $ infer tm


\subsection{Being paranoiac}


The |validateHere| command performs some sanity checks on the current
location, which may be useful for paranoia purposes.

> validateHere :: ProofState ()
> validateHere = do
>     m <- getCurrentEntry
>     case m of
>         CDefinition _ (_ := DEFN tm :<: ty) _ _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: definition type failed to type-check: SET does not admit"
>                              ++ errTyVal (ty :<: SET))
>             tm' <- bquoteHere tm
>             checkHere (ty :>: tm')
>                 `pushError`  (err "validateHere: definition failed to type-check:"
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "does not admit"
>                              ++ errTyVal (tm :<: ty))
>             return ()
>         CDefinition _ (_ := HOLE _ :<: ty) _ _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: hole type failed to type-check: SET does not admit" 
>                              ++ errTyVal (ty :<: SET))
>             return ()
>         _ -> return ()
