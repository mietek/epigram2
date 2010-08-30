\section{The |Elab| monad: a DSL for elaboration}
\label{sec:Elaboration.ElabMonad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards #-}

> module Elaboration.ElabMonad where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import NameSupply.NameSupply

> import Evidences.Tm
> import Evidences.Eval

> import DisplayLang.Name
> import DisplayLang.Scheme

> import Elaboration.ElabProb

%endif

Because writing elaborators is a tricky business, we would like to have a
domain-specific language to write them with. We use the following set of
instructions to define a monad that follows the syntax of this language,
then write an interpreter to run the syntax in the |ProofState| monad.

> eLambda      :: String -> Elab REF
>              -- create a $\lambda$ and return its REF
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
>     =  EReturn x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EWait String TY (EXTM :=>: VAL -> Elab x)
>     |  ECry (StackError DInTmRN)
>     |  EElab Loc EProb
>     |  ECompute (TY :>: Elab (INTM :=>: VAL)) (INTM :=>: VAL -> Elab x)
>     |  EFake ((REF, Spine {TT} REF) -> Elab x)
>     |  EAnchor (String -> Elab x)
>     |  EResolve RelName ((INTM :=>: VAL, Maybe (Scheme INTM)) -> Elab x)
>     |  EAskNSupply (NameSupply -> Elab x)


Now we can define the instructions we wanted:

> eLambda       = flip ELambda EReturn
> eGoal         = EGoal EReturn
> eWait x ty    = EWait x ty EReturn
> eCry          = ECry
> eElab loc p   = EElab loc p
> eCompute      = flip ECompute EReturn
> eFake         = EFake EReturn
> eAnchor       = EAnchor EReturn
> eResolve      = flip EResolve EReturn
> eAskNSupply   = EAskNSupply EReturn

> eFaker :: Elab (EXTM :=>: VAL)
> eFaker = do
>   (r, sp) <- eFake
>   let t = (P r) $:$ sp
>   return (t :=>: evTm t)

We will eventually need to keep track of which elaboration problems correspond
to which source code locations. For the moment, |Loc|s are just ignored.

> newtype Loc = Loc Int deriving Show


%if False

> instance Show x => Show (Elab x) where
>     show (EReturn x)        = "EReturn (" ++ show x ++ ")"
>     show (ELambda s _)      = "ELambda " ++ s ++ " (...)"
>     show (EGoal _)          = "EGoal (...)"
>     show (EWait s ty _)     = "EWait " ++ show s ++ " (" ++ show ty ++ ") (...)"
>     show (ECry _)           = "ECry (...)"
>     show (EElab l tp)       = "EElab " ++ show l ++ " (" ++ show tp ++ ")"
>     show (ECompute te _)    = "ECompute (" ++ show te ++ ") (...)"
>     show (EFake _)          = "EFake " ++ " (...)"
>     show (EAnchor _)        = "EAnchor " ++ " (...)"
>     show (EResolve rn _)    = "EResolve " ++ show rn ++ " (...)"
>     show (EAskNSupply _)    = "EAskNSupply (...)"

> instance Monad Elab where
>     fail s  = ECry [err $ "fail: " ++ s]
>     return  = EReturn
>
>     EReturn x        >>= k = k x
>     ELambda s f      >>= k = ELambda s      ((k =<<) . f)
>     EGoal f          >>= k = EGoal          ((k =<<) . f)
>     EWait s t f      >>= k = EWait s t      ((k =<<) . f)
>     ECry errs        >>= k = ECry errs
>     EElab l p        >>= k = error $ "EElab: cannot bind:\n" ++ show p
>     ECompute te f    >>= k = ECompute te    ((k =<<) . f)
>     EFake f          >>= k = EFake          ((k =<<) . f)
>     EAnchor f        >>= k = EAnchor        ((k =<<) . f)
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
