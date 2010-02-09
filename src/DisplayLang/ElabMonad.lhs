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

> data CProb = ElabProb (Elab VAL) | ResolveProb RelName deriving Show

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
>     show (ECompute ty p _)  = "ECompute (" ++ show ty ++ ") (" ++ show p ++ ") (...)"
>     show (ESolve ref v _)   = "ESolve (" ++ show ref ++ ") (" ++ show v ++ ") (...)"
>     show (EElab ty lp _)    = "EElab (" ++ show ty ++ ") " ++ show lp ++ " (...)"
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
>     ECompute t p f  >>= k = ECompute t p   ((k =<<) . f)
>     ESolve r v f    >>= k = ESolve r v     ((k =<<) . f)
>     EElab t lp f    >>= k = EElab t lp     ((k =<<) . f)
>     ECan v f        >>= k = ECan v         ((k =<<) . f)
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

> runElab :: Elab VAL -> ProofState (Maybe (INTM :=>: VAL))
> runElab (Bale x) = bquoteHere x >>= return . Just . (:=>: x)
> runElab (ELambda s f) = lambdaBoy s >>= runElab . f
> runElab (EGoal f) = getHoleGoal >>= runElab . f . valueOf

> runElab (EHope ty@(PRF (EQBLUE (_S :>: s)
>                          (_T :>: (NP ref@(_ := HOLE Hoping :<: _))))) f) = do
>     ty' <- bquoteHere ty
>     _ :=>: v <- suspend ("hope" :<: ty' :=>: ty) (ESolve ref s $ const . Bale $ pval refl $$ A _S $$ A s)
>     runElab (f v)

> runElab (EHope (PRF p) f) = prove False p >>= runElab . f . valueOf

> runElab (EHope ty f) = do
>     ty' <- bquoteHere ty
>     tm <- make' Hoping ("hope" :<: ty' :=>: ty)
>     runElab . f . valueOf $ tm

> runElab (ECry e)  = throwError e
> runElab (ECompute ty prob f) = runElabCompute ty prob >>= runElab . f

> runElab (ESolve ref val f) = bquoteHere val >>= forceHole ref >>= runElab . f . valueOf

> runElab (ECan (C c) f) = runElab (f c)

> runElab (ECan tm f) = do
>     suspendHere (ECan tm f)
>     return Nothing


> runElabCompute :: TY -> CProb -> ProofState VAL
> runElabCompute ty (ElabProb e) = do
>     ty' <- bquoteHere ty
>     _ :=>: ptv <- make' Waiting ("ElabProb" :<: ty' :=>: ty)
>     goIn
>     mtm <- runElab e
>     case mtm of
>         Just (tm :=>: _)  -> return . valueOf =<< give tm
>         Nothing           -> return ptv
> runElabCompute ty (ResolveProb rn) = do
>     (ref, as, ms) <- elabResolve rn
>     (tm :<: ty) <- inferHere (P ref $:$ as)
>     return (PAIR ty tm)


The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration process to its tip.
When the scheduler hits the goal, the elaboration process will restart.

> suspend :: (String :<: INTM :=>: TY) -> Elab VAL -> ProofState (EXTM :=>: VAL)
> suspend (x :<: tt) elab = do
>     r <- make' Waiting (x :<: tt)
>     Just (E ref xn (Girl LETG (es, Unknown utt, nsupply) ms) tm) <- removeDevEntry
>     putDevEntry (E ref xn (Girl LETG (es, UnknownElab utt elab, nsupply) ms) tm)
>     return r


> suspendHere :: Elab VAL -> ProofState ()
> suspendHere elab = do
>     Unknown tt <- getDevTip
>     putDevTip (UnknownElab tt elab)


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
>     cty <- ECan (tytv $$ Fst) Bale
>     let tv = tytv $$ Snd
>     (s', ty') <- elimTy (chevElab loc) (tv :<: cty) s
>     return $ PAIR ty' (tv $$ fmap valueOf s')

> makeElabInfer loc (DType ty) = do
>     tyv <- ECompute SET (ElabProb (makeElab loc (SET :>: ty))) Bale
>     return $ PAIR (ARR tyv tyv) (idVAL "typecast")


> makeElabInfer loc tm = throwError' $ err "makeElabInfer: can't cope with"
>     ++ errTm (DN tm)


> elmCT :: ExDTmRN -> ProofState String
> elmCT tm = do
>     let el = makeElabInfer (Loc 0) tm
>     suspend ("elab" :<: sigSetTM :=>: sigSetVAL) el
>     cursorTop
>     scheduler 0
>     return "Okay."

> scheduler :: Int -> ProofState ()
> scheduler n = do
>     cs <- getDevCadets
>     case cs of
>         F0      -> if n == 0 then return () else goOutProperly >> scheduler (n-1)
>         E _ _ (Boy _) _ :> _  -> cursorDown >> scheduler n
>         E ref _ (Girl _ (_, UnknownElab tt elab, _) _) _ :> _
>           | isUnstable elab -> do
>             cursorDown
>             goIn
>             putDevTip (Unknown tt)
>             proofTrace $ "scheduler: resuming elaboration on " ++ show (refName ref)
>                 ++ ":\n" ++ show elab
>             mtm <- runElab elab
>             case mtm of
>                 Just (tm :=>: _) -> give' tm >> return ()
>                 Nothing -> proofTrace "scheduler: elaboration suspended."
>             cursorTop
>             scheduler (n+1)
>         _ :> _ -> cursorDown >> goIn >> cursorTop >> scheduler (n+1)
>   where
>     isUnstable :: Elab x -> Bool
>     isUnstable (Bale _) = True
>     isUnstable (ELambda _ _) = True
>     isUnstable (EGoal _) = True
>     isUnstable (EHope _ _) = True
>     isUnstable (ECry _) = True
>     isUnstable (ECompute _ _ _) = True
>     isUnstable (ESolve _ _ _) = True
>     isUnstable (EElab _ _ _) = True
>     isUnstable (ECan (C _) _) = True
>     isUnstable (ECan _ _) = False
>     isUnstable (EEnsure _ _ _) = True


> sigSetTM :: INTM
> sigSetTM = SIGMA SET (idTM "sst")

> sigSetVAL :: VAL
> sigSetVAL = SIGMA SET (idVAL "ssv")


> import -> CochonTactics where
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term> using the Elab monad."