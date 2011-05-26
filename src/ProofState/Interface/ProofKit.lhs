\section{The |ProofState| Kit}
\label{sec:ProofState.Interface.ProofKit}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.ProofKit where

> import Control.Monad.Error
> import Control.Applicative

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.TypeChecker


%endif

> chkPS :: (TY :>: EXP) -> ProofState ()
> chkPS (ty :>: e) = do
>  lev <- getDevLev
>  chk lev (ty :>: (ENil, e))


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

> instance NameSupplier ProofState where
>     freshName s f = do
>         nsupply <- getDevNSupply
>         freshName s ( \n nsupply' -> do
>             putDevNSupply nsupply'
>             f n
>           ) nsupply
>
>     forkNSupply = error "ProofState does not provide forkNSupply"
>     
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply to
proof state commands.

> withNSupply :: (NameSupply -> x) -> ProofState x
> withNSupply f = getDevNSupply >>= return . f

\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


\subsection{Accessing the type-checker}



> checkHere :: (TY :>: EXP) -> ProofState ()
> checkHere (ty :>: tm) = getDevLev >>= \ l -> chk l (ty :>: (ENil, tm))

> inferHere :: EXP -> ProofState TY
> inferHere tt = getDevLev >>= \ l -> inf l (ENil, tt)

> inferSpHere :: (EXP :<: TY) -> [Elim EXP] -> ProofState TY
> inferSpHere ety es = getDevLev >>= \ l -> spInf l ety (ENil , es)

> {-

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

> -}

> validateHere :: ProofState ()
> validateHere = return () -- ha ha ha ha
