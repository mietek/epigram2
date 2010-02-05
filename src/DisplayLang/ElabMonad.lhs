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
< cry : a
< elab : TY -> (LOC, EPROB) -> VAL
< compute : TY -> CPROB -> VAL
< can : VAL -> Can VAL
< solve : REF -> VAL -> REF
< ensure : VAL -> Can () -> (Can VAL, VAL)


> newtype Loc = Loc Int deriving Show

> data EProb = CheckProb () deriving Show

> data CProb x where
>     ElabProb :: Elab x -> CProb x
>     ResolveProb :: RelName -> CProb VAL

> data Elab x
>     =  Bale x
>     |  ELambda String (REF -> Elab x)
>     |  EGoal (TY -> Elab x)
>     |  EHope TY [VAL] ((VAL, [VAL]) -> Elab x)
>     |  ECry (StackError InDTmRN)

>     |  EElab TY  (Loc, EProb) (VAL -> Elab x)
>     |  forall y. ECompute TY (CProb y) (y -> Elab x)
>     |  ECan VAL (Can VAL -> Elab x)
>     |  ESolve REF VAL (REF -> Elab x)
>     |  EEnsure VAL (Can ()) ((Can VAL, VAL) -> Elab x)

> instance Show x => Show (Elab x) where
>     show (Bale x) = "Bale (" ++ show x ++ ")"
>     show (ELambda s _) = "ELambda " ++ s ++ " (...)"
>     show (EGoal _) = "EGoal (...)"
>     show (EHope ty vs _) = "EHope (" ++ show ty ++ ") " ++ show vs ++ " (...)"
>     show (ECry _) = "ECry (...)"
>     show (ECompute ty _ _) = "ECompute (" ++ show ty ++ ") (...) (...)"

> instance Monad Elab where
>     return = Bale
>     Bale x          >>= k = k x
>     ELambda s f     >>= k = ELambda s ((k =<< ) . f)
>     EGoal f         >>= k = EGoal ((k =<<) . f)
>     EHope t vs f    >>= k = EHope t vs ((k =<<) . f)
>     ECry errs       >>= k = ECry errs

>     EElab t lp f    >>= k = EElab t lp ((k =<<) . f)
>     ECompute t p f  >>= k = ECompute t p ((k =<<) . f)
>     ECan v f        >>= k = ECan v ((k =<<) . f)
>     ESolve r v f    >>= k = ESolve r v ((k =<<) . f)
>     EEnsure v c f   >>= k = EEnsure v c ((k =<<) . f)

>     fail s = ECry [err $ "fail: " ++ s]

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


The |runElab| proof state command actually interprets an |Elab x| in
the proof state.

> runElab :: Elab x -> ProofState x
> runElab (Bale x) = return x
> runElab (ELambda s f) = lambdaBoy s >>= runElab . f
> runElab (EGoal f) = getHoleGoal >>= runElab . f . valueOf

> runElab (EHope ty@(PRF (EQBLUE (_T :>: (NP ref@(_ := HOLE Hoping :<: _))) (_S :>: s))) vs f) = do
>     ty' <- bquoteHere ty
>     vs' <- mapM bquoteHere vs
>     s' <- bquoteHere s
>     make' (WaitingFor vs') ("wait" :<: ty' :=>: ty)
>     proofTrace("vs': " ++ show vs')
>     goIn
>     solveHole ref s'
>     GirlMother (_ := HOLE (WaitingFor vs'') :<: _) _ _ _ <- getMother
>     proofTrace ("vs'': " ++ show vs'')
>     goOut
>     runElab (f (pval refl $$ A _S $$ A s, map evTm vs''))


> runElab (EHope ty@(PRF (EQBLUE (_S :>: s) (_T :>: (NP ref@(_ := HOLE Hoping :<: _))))) vs f) = do
>     ty' <- bquoteHere ty
>     vs' <- mapM bquoteHere vs
>     s' <- bquoteHere s
>     make' (WaitingFor vs') ("wait" :<: ty' :=>: ty)
>     proofTrace("vs': " ++ show vs')
>     goIn
>     solveHole ref s'
>     GirlMother (_ := HOLE (WaitingFor vs'') :<: _) _ _ _ <- getMother
>     proofTrace ("vs'': " ++ show vs'')
>     goOut
>     runElab (f (pval refl $$ A _S $$ A s, map evTm vs''))

> runElab (EHope (PRF p) vs f) = do
>     _ :=>: v <- prove False p 
>     runElab (f (v, vs))

> runElab (EHope ty vs f) = do
>     ty' <- bquoteHere ty
>     tm <- make' Hoping ("hope" :<: ty' :=>: ty)
>     runElab (f (valueOf tm, vs))
> runElab (ECry e)  = throwError e
> runElab (ECompute ty prob f) = runElabCompute ty prob >>= runElab . f


> runElabCompute :: TY -> CProb x -> ProofState x
> runElabCompute ty (ElabProb e) = do
>     ty' <- bquoteHere ty
>     make' Waiting ("ElabProb" :<: ty' :=>: ty)
>     goIn
>     x <- runElab e
>     goOut
>     return x
> runElabCompute ty (ResolveProb rn) = do
>     (ref, as, ms) <- elabResolve rn
>     (tm :<: ty) <- inferHere (P ref $:$ as)
>     return (PAIR ty tm)

The |makeElab| function produces an |Elab| in a type-directed way.

> makeElab :: Loc -> (TY :>: InDTmRN) -> Elab VAL

> makeElab loc (ty :>: DU) = EHope ty [] (Bale . fst)

> makeElab loc (C ty :>: DC tm) = do
>     v <- canTy chev (ty :>: tm)
>     return $ C $ fmap valueOf v
>   where
>     chev :: (TY :>: InDTmRN) -> Elab (() :=>: VAL)
>     chev tt = makeElab loc tt >>= return . (() :=>:)

> makeElab loc (PI s (L (K t)) :>: DL (DK dtm)) = do
>     tm <- makeElab loc (t :>: dtm)
>     return (L (K tm))

> makeElab loc (ty :>: DL sc) = do
>     Just (_, s, f) <- return $ lambdable ty
>     tt <- ECompute ty (ElabProb (do
>         ref <- ELambda (dfortran (DL sc)) Bale
>         makeElab loc (s :>: underDScope sc ref)
>       )) Bale
>     return tt -- this is wrong; do we need some kind of discharge command?

> makeElab loc (w :>: DN n) = do
>     PAIR y nv <- makeElabInfer loc n
>     p <- (case opRunEqGreen [SET, y, SET, w] of
>         Right ABSURD ->
>             throwError' $ err "makeElab: inferred type "
>                                             ++ errTyVal (y :<: SET)
>                                             ++ err " of "
>                                             ++ errTyVal (nv :<: y)
>                                             ++ err " is not " 
>                                             ++ errTyVal (w :<: SET)
>         Right p  -> return p
>         Left _   -> return (EQBLUE (SET :>: y) (SET :>: w))
>       ) :: Elab VAL
>     EHope (PRF p) [y, w, nv] (\ (q, [y, w, nv]) -> return (coe @@ [y, w, q, nv]))

> makeElab loc (ty :>: tm) = throwError' $ err "makeElab: can't cope with"
>     ++ errTyVal (ty :<: SET) ++ err " :>: " ++ errTm tm 


> makeElabInfer :: Loc -> ExDTmRN -> Elab VAL
> makeElabInfer loc (DP rn) = ECompute sigSetVAL (ResolveProb rn) Bale

> makeElabInfer loc (t ::$ s) = do
>     PAIR (C ty) tv <- makeElabInfer loc t
>     (s', ty') <- elimTy chev (tv :<: ty) s
>     return $ PAIR ty' (tv $$ fmap valueOf s')
>   where
>     chev :: (TY :>: InDTmRN) -> Elab (() :=>: VAL)
>     chev tt = makeElab loc tt >>= return . (() :=>:)

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
>     x <- runElab el
>     x' <- bquoteHere x
>     d <- prettyHere (sigSetVAL :>: x')
>     proofTrace $ "Elaborated to " ++ renderHouseStyle d
>     give x'
>     return "Okay."


> sigSetTM :: INTM
> sigSetTM = SIGMA SET (idTM "sst")

> sigSetVAL :: VAL
> sigSetVAL = SIGMA SET (idVAL "ssv")


> import -> CochonTactics where
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term> using the Elab monad."