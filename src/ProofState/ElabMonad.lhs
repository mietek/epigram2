\section{The |Elab| Monad}
\label{sec:elab_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}

> module ProofState.ElabMonad where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import Evidences.Tm

> import DisplayLang.DisplayTm

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

> data EProb  =  ElabProb InDTmRN
>             |  ElabInferProb ExDTmRN
>   deriving Show

> data CProb  =  ElabRunProb (Elab VAL)
>             |  ResolveProb RelName
>             |  SubProb (Elab VAL)
>   deriving Show

The command signature given above defines the following free monad, which
gives the syntax for commands.

> data Elab x
>     =  Bale x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EHope TY (VAL -> Elab x)
>     |  EWait String TY (VAL -> Elab x)
>     |  ECry (StackError InDTmRN)
>     |  ECompute TY CProb (VAL -> Elab x)
>     |  ESolve REF VAL (VAL -> Elab x)
>     |  EElab TY  (Loc, EProb) (VAL -> Elab x)
>     |  ECan VAL (Can VAL -> Elab x)
>     |  EFake (VAL -> Elab x)

%if False

> instance Show x => Show (Elab x) where
>     show (Bale x)           = "Bale (" ++ show x ++ ")"
>     show (ELambda s _)      = "ELambda " ++ s ++ " (...)"
>     show (EGoal _)          = "EGoal (...)"
>     show (EHope ty _)       = "EHope (" ++ show ty ++ ") (...)"
>     show (EWait s ty _)     = "EHope " ++ show s ++ " (" ++ show ty ++ ") (...)"
>     show (ECry _)           = "ECry (...)"
>     show (ECompute ty p _)  = "ECompute (" ++ show ty ++ ") (" ++ show p ++ ") (...)"
>     show (ESolve ref v _)   = "ESolve (" ++ show ref ++ ") (" ++ show v ++ ") (...)"
>     show (EElab ty lp _)    = "EElab (" ++ show ty ++ ") " ++ show lp ++ " (...)"
>     show (ECan v _)         = "ECan (" ++ show v ++ ") (...)"
>     show (EFake _)          = "EFake (...)"

> instance Monad Elab where
>     fail s  = ECry [err $ "fail: " ++ s]
>     return  = Bale
>
>     Bale x          >>= k = k x
>     ELambda s f     >>= k = ELambda s      ((k =<<) . f)
>     EGoal f         >>= k = EGoal          ((k =<<) . f)
>     EHope t f       >>= k = EHope t        ((k =<<) . f)
>     EWait s t f     >>= k = EWait s t      ((k =<<) . f)
>     ECry errs       >>= k = ECry errs
>     ECompute t p f  >>= k = ECompute t p   ((k =<<) . f)
>     ESolve r v f    >>= k = ESolve r v     ((k =<<) . f)
>     EElab t lp f    >>= k = EElab t lp     ((k =<<) . f)
>     ECan v f        >>= k = ECan v         ((k =<<) . f)
>     EFake f         >>= k = EFake          ((k =<<) . f)

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