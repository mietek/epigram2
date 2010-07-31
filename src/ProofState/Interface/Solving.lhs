\section{Solving goals}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Solving where

> import Control.Applicative

> import Kit.MissingLibrary

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Lifting
> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter

> import DisplayLang.DisplayTm

> import Evidences.Tm
> import Evidences.Rules

> import {-# SOURCE #-} Elaboration.Wire

%endif



The |apply| command checks if the last entry in the development is a girl $y$ with type
$\Pi S T$ and if so, adds a goal of type $S$ and applies $y$ to it.

> apply :: ProofState (EXTM :=>: VAL)
> apply = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF ref@(name := k :<: (PI s t)) _ _ _ _ -> do
>         s' <- bquoteHere s
>         t' <- bquoteHere (t $$ A s)
>         z :=>: _ <- make ("z" :<: s')
>         make ("w" :<: t')
>         goIn
>         give (N (P ref :$ A (N z)))
>     _ -> throwError' $ err  $ "apply: last entry in the development" 
>                             ++ " must be a girl with a pi-type."

The |done| command checks if the last entry in the development is a girl, and if so,
fills in the goal with this entry.

> done :: ProofState (EXTM :=>: VAL)
> done = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF ref _ _ _ _ -> give (N (P ref))
>     _ -> throwError' $ err "done: last entry in the development must be a girl."

The |give| command checks the provided term has the goal type, and if so, fills in
the goal, updates the reference and goes out. The |giveNext| variant moves to the
next goal (if one exists) instead.

> give :: INTM -> ProofState (EXTM :=>: VAL)
> give tm = give' tm <* goOutBelow

> giveNext :: INTM -> ProofState (EXTM :=>: VAL)
> giveNext tm = give' tm <* (nextGoal <|> goOut)

> give' :: INTM -> ProofState (EXTM :=>: VAL)
> give' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             checkHere (tipTy :>: tm) `pushError`
>                 (err "give: typechecking failed:" ++ errTm (DTIN tm)
>                  ++ err "is not of type" ++ errTyVal (tipTy :<: SET))
>             aus <- getGlobalScope
>             sibs <- getEntriesAbove
>             let tmv = evTm (parBind aus sibs tm)
>             CDefinition kind (name := _ :<: tyv) xn ty <- getCurrentEntry
>             let ref = name := DEFN tmv :<: tyv
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             putCurrentEntry (CDefinition kind ref xn ty)
>             updateRef ref
>             return (applySpine ref aus)
>         _  -> throwError' $ err "give: only possible for incomplete goals."

The |select| command takes a term representing a neutral parameter, makes a new
goal of the same type, and fills it in with the parameter.

> select :: INTM -> ProofState (EXTM :=>: VAL)
> select tm@(N (P (name := k :<: ty))) = do
>     ty' <- bquoteHere ty
>     make (fst (last name) :<: ty')
>     goIn
>     give tm
> select _ = throwError' $ err "select: term is not a parameter."




The |ungawa| command looks for a truly obvious thing to do, and does it.

> ungawa :: ProofState ()
> ungawa =  ignore done <|> ignore apply <|> ignore (lambdaBoy "ug")
>           `pushError` (err "ungawa: no can do.")

