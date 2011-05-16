\section{|ElabProb|: syntactic representation of elaboration problems}
\label{sec:Elaboration.ElabProb}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards #-}

> module Elaboration.ElabProb where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> import Evidences.Tm
> import Evidences.ErrorHandling

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Kit.NatFinVec

%endif


An |ElabProb| is a syntactic representation of an elaboration
problem\index{elaboration problem}. Examples include elaborating
a particular piece of display syntax into an evidence term and waiting for
something to happen before elaboration can proceed. Crucially, an elaboration
problem can be suspended by storing it in the proof state. This allows it to be
left alone until more progress can be made (e.g. because it has been updated
with news, or because the scheduler is free to make some non-local change to
the proof state).

It caches the value representations of terms it contains.
\adam{Is this optimisation actually worth the complication?}

\pierre{I don't understand |ElabSchedule|.}  
\adam{The idea is that |ElabSchedule| makes the scheduler work on other problems 
before coming back to work on this one. It doesn't seem to be used at the moment,
so perhaps we can get rid of it. This data type may need to be redesigned to
allow solution of hoping holes earlier in the elaboration process.}

> data EProb 
>     =  ElabDone EXP 
>        -- succeed with given term
>     |  ElabHope
>        -- hope for a solution to turn up
>     |  ElabProb (DInTm RelName)
>        -- elaborate |In| display term
>     |  ElabInferProb (DExTm RelName)
>        -- elaborate and infer type of |Ex| display term
>     |  WaitCan EXP EProb 
>        -- wait for value to become canonical
>     |  WaitSolve DEF EXP EProb
>        -- wait for reference to be solved with term
>     |  ElabSchedule EProb
>        -- kick off the scheduler

An elaboration problem is said to be \emph{unstable}\index{elaboration
problem!unstable} if the scheduler can make progress on it, and
\emph{stable}\emph{elaboration problem!stable} if not. At present, the
only kind of stable elaboration problem is waiting for a non-canonical
term to become canonical.

\pierre{At this stage, the notion of scheduler has not been
introduced. Therefore, stable or unstable doesn't speak to me. What is
the scheduler doing?}
\adam{We need a general introduction to elaboration, explaining how all the
various components fit together.}

> isUnstable :: EProb -> Bool
> isUnstable (ElabDone _)                                    = True
> isUnstable ElabHope                                        = True
> isUnstable (ElabProb _)                                    = True
> isUnstable (ElabInferProb _)                               = True
> isUnstable (WaitCan tm  _) | _ :- _ <- ev tm               = True
> isUnstable (WaitCan _ _)                                   = False
> isUnstable (WaitSolve _ _ _)                               = True
> isUnstable (ElabSchedule _)                                = True


Since |ElabProb| caches value representations of its terms, we define some handy
functions for producing and manipulating these.


%if False

> instance Show EProb where
>     show (ElabDone tt)            = "ElabDone (" ++ ugly V0 tt ++ ")"
>     show ElabHope                 = "ElabHope"
>     show (ElabProb tm)            = "ElabProb (" ++ show tm ++ ")"
>     show (ElabInferProb tm)       = "ElabInferProb (" ++ show tm ++ ")"
>     show (WaitCan tt prob)        = "WaitCan (" ++ ugly V0 tt ++ ") ("
>                                         ++ show prob ++ ")"
>     show (WaitSolve def tt prob)  = "WaitSolve (D ???) ("
>                                         ++ ugly V0 tt ++ ") (" ++ show prob ++ ")"
>     show (ElabSchedule prob)      = "ElabSchedule (" ++ show prob ++ ")"

%endif

