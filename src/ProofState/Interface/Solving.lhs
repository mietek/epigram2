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
> import Evidences.Eval

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
>             CDefinition kind (name := _ :<: ty) xn tyTm a <- getCurrentEntry
>             let ref = name := DEFN tmv :<: ty
>             putDevTip $ Defined tm $ tipTyTm :=>: tipTy
>             putCurrentEntry $ CDefinition kind ref xn tyTm a
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



\subsection{Finding trivial solutions}


Often, to solve a goal, we make a definition that contains further
developments and, eventually, leads to a solution. To solve the goal,
we are therefore left to |give| this definition. This is the role of
the |done| command that tries to |give| the entry above the cursor.

> done :: ProofState (EXTM :=>: VAL)
> done = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF ref _ _ _ _ _ -> do
>         -- The entry above is indeed a definition
>         giveOutBelow $ NP ref
>     _ -> do
>         -- The entry was not a definition
>         throwError' $ err "done: entry above cursor must be a definition."


Slightly more sophisticated is the well-known |apply| tactic in Coq:
we are trying to solve a goal of type |T| while we have a definition
of type |Pi S T|. We can therefore solve the goal |T| provided we can
solve the goal |S|. We have this tactic too and, guess what, it is
|apply|.

> apply :: ProofState (EXTM :=>: VAL)
> apply = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     EDEF f@(_ := _ :<: (PI _S _T)) _ _ _ _ _ -> do
>         -- The entry above is a proof of |Pi S T|
>
>         -- Ask for a proof of |S|
>         _STm <- bquoteHere _S
>         sTm :=>: s <- make $ "s" :<: _STm
>         -- Make a proof of |T|
>         _TTm <- bquoteHere $ _T $$ A s
>         make $ "t" :<: _TTm
>         goIn
>         giveOutBelow $ N $ P f :$ A (N sTm)
>     _ -> throwError' $ err  $ "apply: last entry in the development" 
>                             ++ " must be a definition with a pi-type."

The |ungawa| command looks for a truly obvious thing to do, and does it.

> ungawa :: ProofState ()
> ungawa =  ignore done <|> ignore apply <|> ignore (lambdaParam "ug")
>           `pushError` (err "ungawa: no can do.")


\subsection{Refining the proof state}

To refine the proof state, we must supply a new goal type and a realiser, which
takes values in the new type to values in the original type. The
|refineProofState| command creates a new subgoal at the top of the working
development, so the entries in that development are not in scope. 

> refineProofState :: INTM -> (EXTM -> INTM) -> ProofState ()
> refineProofState ty realiser = do
>     cursorTop
>     t :=>: _ <- make ("refine" :<: ty)
>     cursorBottom
>     give (realiser t)
>     cursorTop
>     cursorDown
>     goIn