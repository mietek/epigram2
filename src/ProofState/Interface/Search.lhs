\section{Searching in the Proof Context}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Search where

> import Control.Applicative
> import Control.Monad

> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import Evidences.Tm

> import DisplayLang.Name

%endif


In Section~\ref{sec:Proofstate.Edition.Navigation}, we have developped
several commands to navigate in the proof context. Here, we extend
these to be able \emph{search} in the proof context.


\subsection{Searching by name}

The |goTo| command moves the focus to the entry with the given
name. Recall that a long name is an itinerary in the proof context,
listing short names from the root down to the entry. Hence, we simply
have to follow this itinerary to reach our destination.

> goTo :: Name -> ProofState ()
> goTo name = do
>   -- Start from the root
>   goRoot
>   -- Eat the name as you move in the context
>   goTo' name
>   where
>     goTo' :: Name -> ProofState ()
>     goTo'  []          =  do 
>                           -- Reached the end of the journey
>                           return ()
>     goTo'  x@(xn:xns)  =  goIn >> seek xn >> goTo' xns
>                           `pushError` 
>                           (err "goTo: could not find " ++ err (showName x))
>
>     -- |seek| find the local short name on our itinerary
>     seek :: (String, Int) -> ProofState ()
>     seek xn = do
>         goUp `whileA` (guard . (== xn) . last =<< getCurrentName)


\subsection{Searching for a goal}

First off, a \emph{goal} is a development which |Tip| is of the
|Unknown| type. Hence, to spot if the focus is set on a goal, we just
have the check the |Tip|.

> isGoal :: ProofState ()
> isGoal = do
>     Unknown _ <- getDevTip
>     return ()

Let us start with some gymnastic. We implement |prevStep| and
|nextStep| that respectively looks for the previous and the next
definition in the proof context. By \emph{previous}, we mean contained
in an entry directly above, or, if there is none, to the enclosing
development. In other words, it has been defined ``just
\emph{previously}''. The definition transposes to the case of
|nextStep|.

> prevStep :: ProofState ()
> prevStep =  (goUp >> much goIn) <|> goOut
>             `pushError` 
>             (err "prevStep: no previous steps.")
>
> nextStep :: ProofState ()
> nextStep =  (goIn >> goTop) <|> goDown <|> (goOut `untilA` goDown)
>             `pushError` 
>             (err "nextStep: no more steps.")

It is then straightforward to navigate relatively to goals: we move
from steps to steps, looking for a step that would be a goal.

> prevGoal :: ProofState ()
> prevGoal =  prevStep `untilA` isGoal
>             `pushError` 
>             (err "prevGoal: no previous goals.")
>
> nextGoal :: ProofState ()
> nextGoal =  nextStep `untilA` isGoal
>             `pushError` 
>             (err "nextGoal: no more goals.")

In the very spirit of a theorem prover, we sometimes want to stay at
the current location if it is a goal, and go to the next goal
otherwise.

> seekGoal :: ProofState ()
> seekGoal = isGoal <|> nextGoal
