\section{The |Elab| Monad}
\label{sec:elab_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards #-}

> module UI.Cochon.Elaboration.ElabMonad where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Data.Foldable
> import Data.Traversable

> import NameSupply.NameSupply

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme

%endif

\subsection{Defining a DSL}

Because writing elaborators is a tricky business, we would like to have a
domain-specific language to write them with. We use the following set of
instructions to define a monad that follows the syntax of this language,
then write an interpreter to run the syntax in the |ProofState| monad.

> eLambda      :: String -> Elab REF
>              -- create a $\lambda$-boy and return its REF
> eGoal        :: Elab TY
>              -- return the type of the goal
> eWait        :: String -> TY -> Elab (EXTM :=>: VAL)
>              -- create a subgoal corresponding to a question mark
> eCry         :: StackError DInTmRN -> Elab a
>              -- give up with an error
> eElab        :: Loc -> EProb -> Elab a
>              -- solve a suspendable elaboration problem and return the result
> eCompute     :: (TY :>: Elab (INTM :=>: VAL)) -> Elab (INTM :=>: VAL)
>              -- execute commands to produce an element of a given type
> eFake        :: Elab (REF, Spine {TT} REF)
>              -- return a fake reference to the current goal and the current spine
> eResolve     :: RelName -> Elab (INTM :=>: VAL, Maybe (Scheme INTM))
>              -- resolve a name to a term and maybe a scheme
> eAskNSupply  :: Elab NameSupply
>              -- return a fresh name supply


The instruction signature given above is implemented using the following monad.

> data Elab x
>     =  Bale x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EWait String TY (EXTM :=>: VAL -> Elab x)
>     |  ECry (StackError DInTmRN)
>     |  EElab Loc EProb
>     |  ECompute (TY :>: Elab (INTM :=>: VAL)) (INTM :=>: VAL -> Elab x)
>     |  EFake ((REF, Spine {TT} REF) -> Elab x)
>     |  EResolve RelName ((INTM :=>: VAL, Maybe (Scheme INTM)) -> Elab x)
>     |  EAskNSupply (NameSupply -> Elab x)


Now we can define the instructions we wanted:

> eLambda       = flip ELambda Bale
> eGoal         = EGoal Bale
> eWait x ty    = EWait x ty Bale
> eCry          = ECry
> eElab loc p   = EElab loc p
> eCompute      = flip ECompute Bale
> eFake         = EFake Bale
> eResolve      = flip EResolve Bale
> eAskNSupply   = EAskNSupply Bale

> eFaker :: Elab (EXTM :=>: VAL)
> eFaker = do
>   (r, sp) <- eFake
>   let t = (P r) $:$ sp
>   return (t :=>: evTm t)

We will eventually need to keep track of which elaboration problems correspond
to which source code locations. For the moment, |Loc|s are just ignored.

> newtype Loc = Loc Int deriving Show


\subsection{Syntactic representation of elaboration problems}

An |ElabProb| is a syntactic representation of an elaboration problem, which
can be suspended, stored in the proof state and later updated with news. It
caches the value representations of terms it contains.

> data ElabProb x
>     =  ElabDone (InTm x :=>: Maybe VAL)
>        -- succeed with given term
>     |  ElabHope
>        -- hope for a solution to turn up
>     |  ElabProb (DInTm x RelName)
>        -- elaborate |In| display term
>     |  ElabInferProb (DExTm x RelName)
>        -- elaborate and infer type of |Ex| display term
>     |  WaitCan (InTm x :=>: Maybe VAL) (ElabProb x)
>        -- wait for value to become canonical
>     |  WaitSolve x (InTm x :=>: Maybe VAL) (ElabProb x)
>        -- wait for reference to be solved with term
>     |  ElabSchedule (ElabProb x)
>        -- kick off the scheduler

It is a traversable functor, parameterised by the type of references, which
are typically |REF|s. Note that traversal will discard the cached values, but
this is okay because the terms need to be re-evaluated after they have been
updated anyway.

> type EProb = ElabProb REF

An elaboration problem is said to be \emph{unstable} if the scheduler can make
progress on it, and \emph{stable} if not. At present, the only kind of stable
elaboration problem is waiting for a non-canonical term to become canonical.

> isUnstable :: EProb -> Bool
> isUnstable (ElabDone _)                                    = True
> isUnstable ElabHope                                        = True
> isUnstable (ElabProb _)                                    = True
> isUnstable (ElabInferProb _)                               = True
> isUnstable (WaitCan (_ :=>: Just (C _)) _)                 = True
> isUnstable (WaitCan (tm :=>: Nothing) _) | C _ <- evTm tm  = True
> isUnstable (WaitCan _ _)                                   = False
> isUnstable (WaitSolve _ _ _)                               = True
> isUnstable (ElabSchedule _)                                = True



Since |ElabProb| caches value representations of its terms, we define some handy
functions for producing and manipulating these.

> justEval :: INTM :=>: VAL -> INTM :=>: Maybe VAL
> justEval (tm :=>: v) = tm :=>: Just v
>
> maybeEval :: INTM :=>: Maybe VAL -> INTM :=>: VAL
> maybeEval (tm :=>: Just v)   =  tm :=>:  v
> maybeEval (tm :=>: Nothing)  =  tm :=>:  evTm tm


%if False

> instance Show a => Show (ElabProb a) where
>     show (ElabDone tt)            = "ElabDone (" ++ show tt ++ ")"
>     show ElabHope                 = "ElabHope"
>     show (ElabProb tm)            = "ElabProb (" ++ show tm ++ ")"
>     show (ElabInferProb tm)       = "ElabInferProb (" ++ show tm ++ ")"
>     show (WaitCan tt prob)        = "WaitCan (" ++ show tt ++ ") ("
>                                         ++ show prob ++ ")"
>     show (WaitSolve ref tt prob)  = "WaitSolve (" ++ show ref ++ ") ("
>                                         ++ show tt ++ ") (" ++ show prob ++ ")"
>     show (ElabSchedule prob)      = "ElabSchedule (" ++ show prob ++ ")"

> instance Functor ElabProb where
>     fmap = fmapDefault

> instance Foldable ElabProb where
>     foldMap = foldMapDefault

> instance Traversable ElabProb where
>     traverse f (ElabDone tt)            = (|ElabDone (travEval f tt)|)
>     traverse f ElabHope                 = (|ElabHope|)
>     traverse f (ElabProb tm)            = (|ElabProb (traverseDTIN f tm)|)
>     traverse f (ElabInferProb tm)       = (|ElabInferProb (traverseDTEX f tm)|)
>     traverse f (WaitCan tt prob)        = (|WaitCan (travEval f tt) (traverse f prob)|)
>     traverse f (WaitSolve ref tt prob)  = (|WaitSolve (f ref) (travEval f tt) (traverse f prob)|)
>     traverse f (ElabSchedule prob)      = (|ElabSchedule (traverse f prob)|)

> travEval :: Applicative f => (p -> f q) -> InTm p :=>: Maybe VAL -> f (InTm q :=>: Maybe VAL)
> travEval f (tm :=>: _) = (|traverse f tm :=>: ~Nothing|)

The following are essentially saying that |DInTm| is traversable in its first
argument, as well as its second.

> traverseDTIN :: Applicative f => (p -> f q) -> DInTm p x -> f (DInTm q x)
> traverseDTIN f (DL (x ::. tm)) = (|DL (|(x ::.) (traverseDTIN f tm)|)|)
> traverseDTIN f (DL (DK tm)) = (|DL (|DK (traverseDTIN f tm)|)|)
> traverseDTIN f (DC c) = (|DC (traverse (traverseDTIN f) c)|)
> traverseDTIN f (DN n) = (|DN (traverseDTEX f n)|)
> traverseDTIN f (DQ s) = (|(DQ s)|)
> traverseDTIN f DU     = (|DU|)
> traverseDTIN f (DTIN tm) = (|DTIN (traverse f tm)|)
> import <- DInTmTraverse

> traverseDTEX :: Applicative f => (p -> f q) -> DExTm p x -> f (DExTm q x)
> traverseDTEX f (h ::$ as) = (|(traverseDHead f h) ::$ (traverse (traverse (traverseDTIN f)) as)|)

> traverseDHead :: Applicative f => (p -> f q) -> DHead p x -> f (DHead q x)
> traverseDHead f (DP x) = (|(DP x)|)
> traverseDHead f (DType tm) = (|DType (traverseDTIN f tm)|)
> traverseDHead f (DTEX tm) = (|DTEX (traverse f tm)|)


> instance Show x => Show (Elab x) where
>     show (Bale x)           = "Bale (" ++ show x ++ ")"
>     show (ELambda s _)      = "ELambda " ++ s ++ " (...)"
>     show (EGoal _)          = "EGoal (...)"
>     show (EWait s ty _)     = "EWait " ++ show s ++ " (" ++ show ty ++ ") (...)"
>     show (ECry _)           = "ECry (...)"
>     show (EElab l tp)       = "EElab " ++ show l ++ " (" ++ show tp ++ ")"
>     show (ECompute te _)    = "ECompute (" ++ show te ++ ") (...)"
>     show (EFake _)        = "EFake " ++ " (...)"
>     show (EResolve rn _)    = "EResolve " ++ show rn ++ " (...)"
>     show (EAskNSupply _)    = "EAskNSupply (...)"

> instance Monad Elab where
>     fail s  = ECry [err $ "fail: " ++ s]
>     return  = Bale
>
>     Bale x           >>= k = k x
>     ELambda s f      >>= k = ELambda s      ((k =<<) . f)
>     EGoal f          >>= k = EGoal          ((k =<<) . f)
>     EWait s t f      >>= k = EWait s t      ((k =<<) . f)
>     ECry errs        >>= k = ECry errs
>     EElab l p        >>= k = error $ "EElab: cannot bind:\n" ++ show p
>     ECompute te f    >>= k = ECompute te    ((k =<<) . f)
>     EFake f          >>= k = EFake          ((k =<<) . f)
>     EResolve rn f    >>= k = EResolve rn    ((k =<<) . f)
>     EAskNSupply f    >>= k = EAskNSupply    ((k =<<) . f)

> instance Functor Elab where
>     fmap = ap . return
>
> instance Applicative Elab where
>     pure   = return
>     (<*>)  = ap

> instance Alternative Elab where
>     empty          = ECry [err "empty"]
>     ECry _  <|> x  = x
>     x       <|> _  = x

> instance (MonadError (StackError DInTmRN)) Elab where
>     throwError e           = ECry e
>     catchError (ECry e) f  = f e
>     catchError x _         = x

%endif
