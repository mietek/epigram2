\section{The |Elab| Monad}
\label{sec:elab_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}

> module Elaboration.ElabMonad where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import Data.Traversable

> import Evidences.Tm
> import Evidences.Rules

> import DisplayLang.DisplayTm

> import Kit.MissingLibrary

%endif

Because writing elaborators is a tricky business, we would like to have a
domain-specific language to write them with. We use the following set of
commands to define a monad that follows the syntax of this language,
then write an interpreter to run the syntax in the |ProofState| monad.

\begin{description}
\item[|eLambda|] - create a $\lambda$-boy and return its REF
\item[|eGoal|] - return the type of the goal
\item[|eHope|] - hope for any element of a given type
\item[|eWait|] - create a subgoal corresponding to a question mark
\item[|eCry|] - give up with an error
\item[|eElab|] - solve a suspendable elaboration problem and return the result
\item[|eCompute|] - execute commands to produce an element of a given type
\item[|eFake|] - return a fake reference to the current goal
\item[|eResolve|] - resolve a name to a term and maybe a scheme
\item[|eQuote|] - quote a value to produce a term
\item[|eCoerce S T s|] - coerce s : S to produce an element of T, hoping for a
    proof of S == T if necessary
\end{description}


We will eventually need to keep track of which elaboration problems correspond
to which source code locations. For the moment, |Loc|s are just ignored.

> newtype Loc = Loc Int deriving Show


The command signature given above is implemented using the following monad.

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
>     |  EQuote VAL (INTM :=>: VAL -> Elab x)
>     |  ECoerce (INTM :=>: VAL) (INTM :=>: VAL) (INTM :=>: VAL)
>            (INTM :=>: VAL -> Elab x)


> eLambda :: String -> Elab REF
> eLambda = flip ELambda Bale

> eGoal :: Elab TY
> eGoal = EGoal Bale

> eHope :: TY -> Elab (INTM :=>: VAL)
> eHope = flip EHope Bale

> eWait :: String -> TY -> Elab (EXTM :=>: VAL)
> eWait x ty = EWait x ty Bale

> eCry :: StackError InDTmRN -> Elab a
> eCry = ECry

> eElab :: Loc -> (TY :>: EProb) -> Elab (INTM :=>: VAL)
> eElab loc tp = EElab loc tp Bale

> eCompute :: (TY :>: Elab (INTM :=>: VAL)) -> Elab (INTM :=>: VAL)
> eCompute = flip ECompute Bale

> eFake :: Bool -> Elab (EXTM :=>: VAL)
> eFake = flip EFake Bale

> eResolve :: RelName -> Elab (INTM :=>: VAL, Maybe (Scheme INTM))
> eResolve = flip EResolve Bale

> eQuote :: VAL -> Elab (INTM :=>: VAL)
> eQuote = flip EQuote Bale

> eCoerce :: INTM :=>: VAL -> INTM :=>: VAL -> INTM :=>: VAL -> Elab (INTM :=>: VAL)
> eCoerce _S _T s = ECoerce _S _T s Bale


An |EProb| is a syntactic representation of an elaboration problem, which
can be suspended and later updated with news. Problems may be:
\begin{description}
\item[|ElabDone|] - succeed with the given term
\item[|ElabProb|] - elaborate some |In| display syntax
\item[|ElabInferProb|] - elaborate and infer the type of some |Ex| display syntax
\item[|WaitCan|] - wait for the given term to become canonical before proceeding
\item[|WaitSolve|] - wait for the reference to be solved with the given term
\end{description}

> data EProb  =  ElabDone (INTM :=>: VAL)
>             |  ElabProb InDTmRN
>             |  ElabInferProb ExDTmRN
>             |  WaitCan (INTM :=>: VAL) EProb
>             |  WaitSolve REF (INTM :=>: VAL) EProb
>   deriving Show

An elaboration problem is said to be \emph{unstable} if the scheduler can make
progress on it, and \emph{stable} if not. At present, the only kind of stable
elaboration problem is waiting for a non-canonical term to become canonical.

> isUnstable :: EProb -> Bool
> isUnstable (ElabDone _) = True
> isUnstable (ElabProb _) = True
> isUnstable (ElabInferProb _) = True
> isUnstable (WaitCan (_ :=>: C _) _) = True
> isUnstable (WaitCan _ _) = False
> isUnstable (WaitSolve _ _ _) = True


Since |EProb|s are full of terms, we can update their references using
a |traverse|-like operation.

> traverseEProb :: Applicative f => (REF -> f REF) -> EProb -> f EProb
> traverseEProb f (ElabDone tt) = (|ElabDone (travEval f tt)|)
> traverseEProb f (ElabProb tm) = (|ElabProb (traverseDTIN f tm)|)
> traverseEProb f (ElabInferProb tm) = (|ElabInferProb (traverseDTEX f tm)|)
> traverseEProb f (WaitCan tt prob) = (|WaitCan (travEval f tt) (traverseEProb f prob)|)
> traverseEProb f (WaitSolve ref tt prob) = (|WaitSolve (f ref) (travEval f tt) (traverseEProb f prob)|)

> travEval :: Applicative f => (REF -> f REF) -> INTM :=>: VAL -> f (INTM :=>: VAL)
> travEval f (tm :=>: _) = (|tm' :=>: (|evTm tm'|)|)
>     where tm' = traverse f tm

> traverseDTIN :: Applicative f => (REF -> f REF) -> InDTm x -> f (InDTm x)
> traverseDTIN f (DL (x ::. tm)) = (|DL (|(x ::.) (traverseDTIN f tm)|)|)
> traverseDTIN f (DL (DK tm)) = (|DL (|DK (traverseDTIN f tm)|)|)
> traverseDTIN f (DC c) = (|DC (traverse (traverseDTIN f) c)|)
> traverseDTIN f (DN n) = (|DN (traverseDTEX f n)|)
> traverseDTIN f (DQ s) = (|(DQ s)|)
> traverseDTIN f DU     = (|DU|)
> traverseDTIN f (DTIN tm) = (|DTIN (traverse f tm)|)

> traverseDTEX :: Applicative f => (REF -> f REF) -> ExDTm x -> f (ExDTm x)
> traverseDTEX f (h ::$ as) = (|(traverseDHead f h) ::$ (traverse (traverse (traverseDTIN f)) as)|)

> traverseDHead :: Applicative f => (REF -> f REF) -> DHead x -> f (DHead x)
> traverseDHead f (DP x) = (|(DP x)|)
> traverseDHead f (DType tm) = (|DType (traverseDTIN f tm)|)
> traverseDHead f (DTEX tm) = (|DTEX (traverse f tm)|)


> mapEProb :: (REF -> REF) -> EProb -> EProb
> mapEProb f = ala Id traverseEProb f


%if False

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
>     show (EQuote q _)       = "EQuote (" ++ show q ++ ") (...)"
>     show (ECoerce (s :=>: _) (t :=>: _) (u :=>: _) _) = "ECoerce (" ++ show s ++ ") (" ++ show t ++ ") (" ++ show u ++ ") (...)"

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
>     EQuote q f       >>= k = EQuote q       ((k =<<) . f)
>     ECoerce s t v f  >>= k = ECoerce s t v  ((k =<<) . f)

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