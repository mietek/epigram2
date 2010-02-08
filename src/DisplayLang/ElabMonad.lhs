\section{The |Elab| Monad}
\label{sec:elab_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances,
>     MultiParamTypeClasses, FlexibleInstances,
>     ExistentialQuantification #-}

> module DisplayLang.ElabMonad where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.Developments
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.DisplayMangler
> import DisplayLang.Elaborator
> import DisplayLang.Naming
> import DisplayLang.PrettyPrint

> import Tactics.Information
> import Tactics.Solution

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

Because writing elaborators is a tricky business, we would like to have a
domain-specific language to write them with. We use the following set of
commands to define a monad that follows the syntax of this language,
then write an interpreter to run the syntax in the |ProofState| monad.

< lambda : String -> REF
< goal : TY
< hope : TY -> VAL
< cry : StackError -> a
< elab : TY -> (Loc, EProb) -> VAL
< compute : TY -> CProb -> VAL
< can : VAL -> Can VAL
< solve : REF -> VAL -> REF
< ensure : VAL -> Can () -> (Can VAL, VAL)

We will eventually need to keep track of which elaboration problems correspond
to which source code locations.

> newtype Loc = Loc Int deriving Show

> data EProb = CheckProb () deriving Show

> data CProb = ElabProb (Elab VAL) | ResolveProb RelName

The command signature given above defines the following free monad, which
gives the syntax for commands.

> data Elab x
>     =  Bale x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EHope TY (VAL -> Elab x)
>     |  ECry (StackError InDTmRN)
>     |  ECompute TY CProb (VAL -> Elab x)
>     |  ESolve REF VAL (VAL -> Elab x)

>     |  EElab TY  (Loc, EProb) (VAL -> Elab x)
>     |  ECan VAL (Can VAL -> Elab x)
>     |  EEnsure VAL (Can ()) ((Can VAL, VAL) -> Elab x)

%if False

> instance Show x => Show (Elab x) where
>     show (Bale x)           = "Bale (" ++ show x ++ ")"
>     show (ELambda s _)      = "ELambda " ++ s ++ " (...)"
>     show (EGoal _)          = "EGoal (...)"
>     show (EHope ty _)       = "EHope (" ++ show ty ++ ") (...)"
>     show (ECry _)           = "ECry (...)"
>     show (ECompute ty _ _)  = "ECompute (" ++ show ty ++ ") (...) (...)"
>     show (ESolve ref v _)   = "ESolve (" ++ show ref ++ ") (" ++ show v ++ ") (...)"
>     show (ECan v _)         = "ECan (" ++ show v ++ ") (...)"
>     show (EEnsure v c _)    = "EEnsure (" ++ show v ++ ") (" ++ show c ++ ") (...)"

> instance Monad Elab where
>     fail s  = ECry [err $ "fail: " ++ s]
>     return  = Bale
>
>     Bale x          >>= k = k x
>     ELambda s f     >>= k = ELambda s      ((k =<<) . f)
>     EGoal f         >>= k = EGoal          ((k =<<) . f)
>     EHope t  f      >>= k = EHope t        ((k =<<) . f)
>     ECry errs       >>= k = ECry errs
>     EElab t lp f    >>= k = EElab t lp     ((k =<<) . f)
>     ECompute t p f  >>= k = ECompute t p   ((k =<<) . f)
>     ECan v f        >>= k = ECan v         ((k =<<) . f)
>     ESolve r v f    >>= k = ESolve r v     ((k =<<) . f)
>     EEnsure v c f   >>= k = EEnsure v c    ((k =<<) . f)

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

%endif


The |runElab| proof state command actually interprets an |Elab x| in
the proof state. That is, it defines the semantics of the |Elab| syntax.

> runElab :: Elab VAL -> ProofState (INTM :=>: VAL)
> runElab (Bale x) = bquoteHere x >>= return . (:=>: x)
> runElab (ELambda s f) = lambdaBoy s >>= runElab . f
> runElab (EGoal f) = getHoleGoal >>= runElab . f . valueOf

> runElab (EHope ty@(PRF (EQBLUE (_S :>: s) (_T :>: (NP ref@(_ := HOLE Hoping :<: _))))) f) =
>     (suspend ty $ ESolve ref s $ const . Bale $ pval refl $$ A _S $$ A s)
>     >>= runElab . f

> runElab (EHope (PRF p) f) = prove False p >>= runElab . f . valueOf

> runElab (EHope ty f) = do
>     ty' <- bquoteHere ty
>     tm <- make' Hoping ("hope" :<: ty' :=>: ty)
>     runElab . f . valueOf $ tm

> runElab (ECry e)  = throwError e
> runElab (ECompute ty prob f) = runElabCompute ty prob >>= runElab . f

> runElab (ESolve ref val f) = bquoteHere val >>= solveHole ref >>= runElab . f . valueOf

> runElab (ECan (C c) f) = runElab (f c)


> runElabCompute :: TY -> CProb -> ProofState VAL
> runElabCompute ty (ElabProb e) = do
>     ty' <- bquoteHere ty
>     make' Waiting ("ElabProb" :<: ty' :=>: ty)
>     goIn
>     tm :=>: _ <- runElab e
>     return . valueOf =<< give tm
> runElabCompute ty (ResolveProb rn) = do
>     (ref, as, ms) <- elabResolve rn
>     (tm :<: ty) <- inferHere (P ref $:$ as)
>     return (PAIR ty tm)


The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration process to its tip.
When a news update hits the goal, the elaboration process will restart.

> suspend :: TY -> Elab VAL -> ProofState VAL
> suspend ty elab = do
>     ty' <- bquoteHere ty
>     _ :=>: v <- make' Waiting ("suspend" :<: ty' :=>: ty)
>     Just (E ref xn (Girl LETG (es, Unknown tt, nsupply) ms) tm) <- removeDevEntry
>     putDevEntry (E ref xn (Girl LETG (es, UnknownElab tt elab, nsupply) ms) tm)
>     return v



The |chevElab| helper function is a checker-evaluator version of |makeElab|
that can be passed to |canTy| and |elimTy|. It creates appropriate subgoals
for each component and continues elaborating.

> chevElab :: Loc -> (TY :>: InDTmRN) -> Elab (() :=>: VAL)
> chevElab loc (ty :>: tm) = ECompute ty (ElabProb (makeElab loc (ty :>: tm)))
>                            (return . (() :=>:))


The |makeElab| function produces an |Elab| in a type-directed way.

> makeElab :: Loc -> (TY :>: InDTmRN) -> Elab VAL

> makeElab loc (ty :>: DU) = EHope ty Bale
> makeElab loc (ty :>: DQ _) = EHope ty Bale

> makeElab loc (C ty :>: DC tm) = do
>     v <- canTy (chevElab loc) (ty :>: tm)
>     return $ C $ fmap valueOf v

> makeElab loc (PI s (L (K t)) :>: DL (DK dtm)) = do
>     tm <- makeElab loc (t :>: dtm)
>     return (L (K tm))

> makeElab loc (ty :>: DL sc) = do
>     Just (_, s, f) <- return $ lambdable ty
>     ref <- ELambda (dfortran (DL sc)) Bale
>     makeElab loc (s :>: underDScope sc ref)

> makeElab loc (w :>: DN n) = do
>     yn <- makeElabInfer loc n
>     q <- EHope (PRF (EQBLUE (SET :>: yn $$ Fst) (SET :>: w))) Bale
>     return (coe @@ [yn $$ Fst, w, q, yn $$ Snd])

> makeElab loc (ty :>: tm) = throwError' $ err "makeElab: can't cope with"
>     ++ errTyVal (ty :<: SET) ++ err " :>: " ++ errTm tm 


> makeElabInfer :: Loc -> ExDTmRN -> Elab VAL
> makeElabInfer loc (DP rn) = ECompute sigSetVAL (ResolveProb rn) Bale

> makeElabInfer loc (t ::$ s) = do
>     tytv <- makeElabInfer loc t
>     let tv = tytv $$ Snd
>     case tytv $$ Fst of
>         C cty -> do
>             (s', ty') <- elimTy (chevElab loc) (tv :<: cty) s
>             return $ PAIR ty' (tv $$ fmap valueOf s')
>         ty -> case s of
>             A a -> do
>                 s <- EHope SET Bale
>                 t <- EHope (PI s (LK SET)) Bale
>                 q <- EHope (PRF (EQBLUE (SET :>: PI s t) (SET :>: ty))) Bale
>                 av <- makeElab loc (s :>: a)
>                 return $ PAIR (t $$ A av) (tv $$ A av)
>             _ -> throwError' $ err "I give up."

> makeElabInfer loc (DType ty) = do
>     tyv <- ECompute SET (ElabProb (makeElab loc (SET :>: ty))) Bale
>     return $ PAIR (ARR tyv tyv) (idVAL "typecast")


> makeElabInfer loc tm = throwError' $ err "makeElabInfer: can't cope with"
>     ++ errTm (DN tm)


> elmCT :: ExDTmRN -> ProofState String
> elmCT tm = do
>     let el = makeElabInfer (Loc 0) tm
>     make ("elab" :<: sigSetTM)
>     goIn
>     tm :=>: _ <- runElab el
>     proofTrace $ "Elaborated to " ++ show tm
>     d <- prettyHere (sigSetVAL :>: tm)
>     proofTrace $ "or, more prettily, " ++ renderHouseStyle d
>     give tm
>     return "Okay."


> sigSetTM :: INTM
> sigSetTM = SIGMA SET (idTM "sst")

> sigSetVAL :: VAL
> sigSetVAL = SIGMA SET (idVAL "ssv")


> import -> CochonTactics where
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term> using the Elab monad."