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

< lambda : String -> REF
< goal : TY
< hope : TY -> VAL
< wait : String -> TY -> VAL
< cry : StackError -> a
< elab : TY -> (Loc, EProb) -> VAL
< compute : TY -> CProb -> VAL
< can : VAL -> Can VAL
< solve : REF -> VAL -> REF
< ensure : VAL -> Can () -> (Can VAL, VAL)

We will eventually need to keep track of which elaboration problems correspond
to which source code locations.

> newtype Loc = Loc Int deriving Show

> data EProb  =  ElabDone (INTM :=>: VAL)
>             |  ElabProb InDTmRN
>             |  ElabInferProb ExDTmRN
>             |  WaitCan (INTM :=>: VAL) EProb
>             |  WaitSolve REF (INTM :=>: VAL) EProb
>   deriving Show

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


> isUnstable :: EProb -> Bool
> isUnstable (ElabDone _) = True
> isUnstable (ElabProb _) = True
> isUnstable (ElabInferProb _) = True
> isUnstable (WaitCan (_ :=>: C _) _) = True
> isUnstable (WaitCan _ _) = False
> isUnstable (WaitSolve _ _ _) = True


> data CProb  = SubProb (Elab (INTM :=>: VAL))
>   deriving Show

The command signature given above defines the following monad, which
gives the syntax for commands.

> data Elab x
>     =  Bale x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EHope TY (INTM :=>: VAL -> Elab x)
>     |  EWait String TY (EXTM :=>: VAL -> Elab x)
>     |  ECry (StackError InDTmRN)
>     |  EElab Loc (TY :>: EProb) (INTM :=>: VAL -> Elab x)
>     |  EFake Bool (EXTM :=>: VAL -> Elab x)
>     |  EResolve RelName ((INTM :=>: VAL, Maybe (Scheme INTM)) -> Elab x)
>     |  EQuote VAL (INTM :=>: VAL -> Elab x)
>     |  ECoerce (INTM :=>: VAL) (INTM :=>: VAL) (INTM :=>: VAL)
>            (INTM :=>: VAL -> Elab x)

%if False

> instance Show x => Show (Elab x) where
>     show (Bale x)           = "Bale (" ++ show x ++ ")"
>     show (ELambda s _)      = "ELambda " ++ s ++ " (...)"
>     show (EGoal _)          = "EGoal (...)"
>     show (EHope ty _)       = "EHope (" ++ show ty ++ ") (...)"
>     show (EWait s ty _)     = "EHope " ++ show s ++ " (" ++ show ty ++ ") (...)"
>     show (ECry _)           = "ECry (...)"
>     show (EElab l tp _)     = "EElab " ++ show l ++ " (" ++ show tp ++ ") (...)"
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