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


\subsection{Giving a solution}


The |give| command takes a term and solves the current goal with it,
if it type-checks. At the end of the operation, the cursor has not
moved: we are still under the goal, which has now been |Defined|. Note
that entries below the cursor are (lazily) notified of the good news.

> give :: INTM -> ProofState (EXTM :=>: VAL)
> give tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             -- Working on a goal
>
>             -- The |tm| is of the expected type
>             checkHere (tipTy :>: tm) 
>                 `pushError`
>                 (err "give: typechecking failed:" ++ errTm (DTIN tm)
>                  ++ err "is not of type" ++ errTyVal (tipTy :<: SET))
>             -- Lambda lift the given solution
>             globalScope <- getGlobalScope
>             above <- getEntriesAbove
>             let tmv = evTm $ parBind globalScope above tm
>             -- Update the entry as Defined, together with its definition
>             CDefinition kind (name := _ :<: ty) xn tyTm <- getCurrentEntry
>             let ref = name := DEFN tmv :<: ty
>             putDevTip $ Defined tm $ tipTyTm :=>: tipTy
>             putCurrentEntry $ CDefinition kind ref xn tyTm
>             -- Propagate the good news
>             updateRef ref
>             -- Return the reference
>             return $ applySpine ref globalScope
>         _  -> throwError' $ err "give: only possible for incomplete goals."

For convenience, we combine giving a solution and moving. Indeed,
after |give|, the cursor stands in a rather boring position: under a
|Defined| entry, with no work to do. So, a first variant is
|giveOutBelow| that gives a solution and moves just below the
now-defined entry. A second variant is |giveNext| that gives as well
and moves to the next goal, if one is available.

> giveOutBelow :: INTM -> ProofState (EXTM :=>: VAL)
> giveOutBelow tm = give tm <* goOutBelow
>
> giveNext :: INTM -> ProofState (EXTM :=>: VAL)
> giveNext tm = give tm <* (nextGoal <|> goOut)



\subsection{}

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
>         giveOutBelow (N (P ref :$ A (N z)))
>     _ -> throwError' $ err  $ "apply: last entry in the development" 
>                             ++ " must be a girl with a pi-type."

The |done| command checks if the last entry in the development is a girl, and if so,
fills in the goal with this entry.

> done :: ProofState (EXTM :=>: VAL)
> done = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF ref _ _ _ _ -> giveOutBelow (N (P ref))
>     _ -> throwError' $ err "done: last entry in the development must be a girl."

The |select| command takes a term representing a neutral parameter, makes a new
goal of the same type, and fills it in with the parameter.

> select :: INTM -> ProofState (EXTM :=>: VAL)
> select tm@(N (P (name := k :<: ty))) = do
>     ty' <- bquoteHere ty
>     make (fst (last name) :<: ty')
>     goIn
>     giveOutBelow tm
> select _ = throwError' $ err "select: term is not a parameter."

The |ungawa| command looks for a truly obvious thing to do, and does it.

> ungawa :: ProofState ()
> ungawa =  ignore done <|> ignore apply <|> ignore (lambdaParam "ug")
>           `pushError` (err "ungawa: no can do.")

