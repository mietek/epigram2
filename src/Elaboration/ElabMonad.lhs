\section{The |Elab| Monad}
\label{sec:elab_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards #-}

> module Elaboration.ElabMonad where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Data.Foldable
> import Data.Traversable

> import NameSupply.NameSupply

> import Evidences.Tm
> import Evidences.Rules

> import DisplayLang.DisplayTm

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
> eHope        :: TY -> Elab (INTM :=>: VAL) 
>              -- hope for any element of a given type
> eWait        :: String -> TY -> Elab (EXTM :=>: VAL)
>              -- create a subgoal corresponding to a question mark
> eCry         :: StackError InDTmRN -> Elab a
>              -- give up with an error
> eElab        :: Loc -> (TY :>: EProb) -> Elab (INTM :=>: VAL)
>              -- solve a suspendable elaboration problem and return the result
> eCompute     :: (TY :>: Elab (INTM :=>: VAL)) -> Elab (INTM :=>: VAL)
>              -- execute commands to produce an element of a given type
> eFake        :: Bool -> Elab (EXTM :=>: VAL)
>              -- return a fake reference to the current goal
> eResolve     :: RelName -> Elab (INTM :=>: VAL, Maybe (Scheme INTM))
>              -- resolve a name to a term and maybe a scheme
> eAskNSupply  :: Elab NameSupply
>              -- return a fresh name supply


The instruction signature given above is implemented using the following monad.

> data Elab x
>     =  Bale x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EHope TY (INTM :=>: VAL -> Elab x)
>     |  EWait String TY (EXTM :=>: VAL -> Elab x)
>     |  ECry (StackError InDTmRN)
>     |  EElab Loc (TY :>: EProb) (INTM :=>: VAL -> Elab x)
>     |  ECompute (TY :>: Elab (INTM :=>: VAL)) (INTM :=>: VAL -> Elab x)
>     |  EFake Bool (EXTM :=>: VAL -> Elab x)
>     |  EResolve RelName ((INTM :=>: VAL, Maybe (Scheme INTM)) -> Elab x)
>     |  EAskNSupply (NameSupply -> Elab x)


Now we can define the instructions we wanted:

> eLambda       = flip ELambda Bale
> eGoal         = EGoal Bale
> eHope         = flip EHope Bale
> eWait x ty    = EWait x ty Bale
> eCry          = ECry
> eElab loc tp  = EElab loc tp Bale
> eCompute      = flip ECompute Bale
> eFake         = flip EFake Bale
> eResolve      = flip EResolve Bale
> eAskNSupply   = EAskNSupply Bale


We will eventually need to keep track of which elaboration problems correspond
to which source code locations. For the moment, |Loc|s are just ignored.

> newtype Loc = Loc Int deriving Show


\subsection{Syntactic representation of elaboration problems}

An |ElabProb| is a syntactic representation of an elaboration problem, which
can be suspended, stored in the proof state and later updated with news. It
caches the value representations of terms it contains.

> data ElabProb x
>     =  ElabDone (InTm x :=>: Maybe VAL)                  -- succeed with given term
>     |  ElabProb (InDTm x RelName)                        -- elaborate |In| display term
>     |  ElabInferProb (ExDTm x RelName)                   -- elaborate and infer type of |Ex| display term
>     |  WaitCan (InTm x :=>: Maybe VAL) (ElabProb x)      -- wait for value to become canonical
>     |  WaitSolve x (InTm x :=>: Maybe VAL) (ElabProb x)  -- wait for reference to be solved with term
>   deriving Show

It is a traversable functor, parameterised by the type of references, which
are typically |REF|s. Note that traversal will discard the cached values, but
this is okay because the terms need to be re-evaluated after they have been
updated anyway.

> type EProb = ElabProb REF

An elaboration problem is said to be \emph{unstable} if the scheduler can make
progress on it, and \emph{stable} if not. At present, the only kind of stable
elaboration problem is waiting for a non-canonical term to become canonical.

> isUnstable :: EProb -> Bool
> isUnstable (ElabDone _)              = True
> isUnstable (ElabProb _)              = True
> isUnstable (ElabInferProb _)         = True
> isUnstable (WaitCan (_ :=>: Just (C _)) _)  = True
> isUnstable (WaitCan (tm :=>: Nothing) _) | C _ <- evTm tm  = True
> isUnstable (WaitCan _ _)             = False
> isUnstable (WaitSolve _ _ _)         = True


Since |ElabProb| caches value representations of its terms, we define some handy
functions for producing and manipulating these.

> justEval :: INTM :=>: VAL -> INTM :=>: Maybe VAL
> justEval (tm :=>: v) = tm :=>: Just v
>
> maybeEval :: INTM :=>: Maybe VAL -> INTM :=>: VAL
> maybeEval (tm :=>: Just v)   =  tm :=>:  v
> maybeEval (tm :=>: Nothing)  =  tm :=>:  evTm tm


%if False

> instance Functor ElabProb where
>     fmap = fmapDefault

> instance Foldable ElabProb where
>     foldMap = foldMapDefault

> instance Traversable ElabProb where
>     traverse f (ElabDone tt)            = (|ElabDone (travEval f tt)|)
>     traverse f (ElabProb tm)            = (|ElabProb (traverseDTIN f tm)|)
>     traverse f (ElabInferProb tm)       = (|ElabInferProb (traverseDTEX f tm)|)
>     traverse f (WaitCan tt prob)        = (|WaitCan (travEval f tt) (traverse f prob)|)
>     traverse f (WaitSolve ref tt prob)  = (|WaitSolve (f ref) (travEval f tt) (traverse f prob)|)

> travEval :: Applicative f => (p -> f q) -> InTm p :=>: Maybe VAL -> f (InTm q :=>: Maybe VAL)
> travEval f (tm :=>: _) = (|traverse f tm :=>: ~Nothing|)

The following are essentially saying that |InDTm| is traversable in its first
argument, as well as its second.

> traverseDTIN :: Applicative f => (p -> f q) -> InDTm p x -> f (InDTm q x)
> traverseDTIN f (DL (x ::. tm)) = (|DL (|(x ::.) (traverseDTIN f tm)|)|)
> traverseDTIN f (DL (DK tm)) = (|DL (|DK (traverseDTIN f tm)|)|)
> traverseDTIN f (DC c) = (|DC (traverse (traverseDTIN f) c)|)
> traverseDTIN f (DN n) = (|DN (traverseDTEX f n)|)
> traverseDTIN f (DQ s) = (|(DQ s)|)
> traverseDTIN f DU     = (|DU|)
> traverseDTIN f (DTIN tm) = (|DTIN (traverse f tm)|)

> traverseDTEX :: Applicative f => (p -> f q) -> ExDTm p x -> f (ExDTm q x)
> traverseDTEX f (h ::$ as) = (|(traverseDHead f h) ::$ (traverse (traverse (traverseDTIN f)) as)|)

> traverseDHead :: Applicative f => (p -> f q) -> DHead p x -> f (DHead q x)
> traverseDHead f (DP x) = (|(DP x)|)
> traverseDHead f (DType tm) = (|DType (traverseDTIN f tm)|)
> traverseDHead f (DTEX tm) = (|DTEX (traverse f tm)|)


> instance Show x => Show (Elab x) where
>     show (Bale x)           = "Bale (" ++ show x ++ ")"
>     show (ELambda s _)      = "ELambda " ++ s ++ " (...)"
>     show (EGoal _)          = "EGoal (...)"
>     show (EHope ty _)       = "EHope (" ++ show ty ++ ") (...)"
>     show (EWait s ty _)     = "EHope " ++ show s ++ " (" ++ show ty ++ ") (...)"
>     show (ECry _)           = "ECry (...)"
>     show (EElab l tp _)     = "EElab " ++ show l ++ " (" ++ show tp ++ ") (...)"
>     show (ECompute te _)    = "ECompute (" ++ show te ++ ") (...)"
>     show (EFake b _)        = "EFake " ++ show b ++ " (...)"
>     show (EResolve rn _)    = "EResolve " ++ show rn ++ " (...)"
>     show (EAskNSupply _)    = "EAskNSupply (...)"

> instance Monad Elab where
>     fail s  = ECry [err $ "fail: " ++ s]
>     return  = Bale
>
>     Bale x           >>= k = k x
>     ELambda s f      >>= k = ELambda s      ((k =<<) . f)
>     EGoal f          >>= k = EGoal          ((k =<<) . f)
>     EHope t f        >>= k = EHope t        ((k =<<) . f)
>     EWait s t f      >>= k = EWait s t      ((k =<<) . f)
>     ECry errs        >>= k = ECry errs
>     EElab l tp f     >>= k = EElab l tp     ((k =<<) . f)
>     ECompute te f    >>= k = ECompute te    ((k =<<) . f)
>     EFake b f        >>= k = EFake b        ((k =<<) . f)
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

> instance (MonadError (StackError InDTmRN)) Elab where
>     throwError e           = ECry e
>     catchError (ECry e) f  = f e
>     catchError x _         = x


> newtype WrapElab x = WrapElab {unWrapElab :: Elab x}
>     deriving (Functor, Applicative, Alternative, Monad)

> instance (MonadError (StackError ())) WrapElab where
>     throwError e = WrapElab (throwError [err "WrapElab: cannot unwrap error."])
>     catchError _ _ = WrapElab (throwError [err "WrapElab: cannot catch error."])

%endif