\section{Implementing the |Elab| Monad}
\label{sec:implementing_elab_monad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Elaboration.ElabLanguage where

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.Developments
> import ProofState.ElabMonad
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm

> import Tactics.Solution

> import Elaboration.Elaborator

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


The |runElab| proof state command actually interprets an |Elab x| in
the proof state. That is, it defines the semantics of the |Elab| syntax.

> runElab :: Elab VAL -> ProofState (Maybe (INTM :=>: VAL))
> runElab (Bale x)            = bquoteHere x >>= return . Just . (:=>: x)
> runElab (ELambda s f)       = lambdaBoy s >>= runElab . f
> runElab (EGoal f)           = getHoleGoal >>= runElab . f . valueOf
> runElab (EHope ty f)        = runElabHope ty >>= runElab . f . valueOf
> runElab (ECompute ty p f)   = runElabCompute ty p >>= runElab . f
> runElab (ESolve ref val f)  = bquoteHere val >>= forceHole ref >>= runElab . f . valueOf
> runElab (EElab ty (l,p) f)  = runElabElab ty l p >>= runElab . (>>= f)
> runElab (ECan (C c) f)      = runElab (f c)
> runElab (ECan tm f)         = suspendMe (ECan tm f)
> runElab (ECry e)            = do
>     e' <- distillErrors e
>     let msg = show (prettyStackError e')
>     putHoleKind (Crying msg)
>     return Nothing

The |EHope| command hopes for an element of a given type. If it is asking for a
proof, we might be able to find one, but otherwise we just create a hole.

> runElabHope :: TY -> ProofState (INTM :=>: VAL)
> runElabHope ty@(PRF (EQBLUE (_S :>: s) (_T :>: (NP ref@(_ := HOLE Hoping :<: _))))) = do
>     ty' <- bquoteHere ty
>     neutralise =<< suspend ("hope" :<: ty' :=>: ty)
>         (ESolve ref s $ const . Bale $ pval refl $$ A _S $$ A s)
> runElabHope (PRF p) = prove False p
> runElabHope ty = do
>     ty' <- bquoteHere ty
>     neutralise =<< make' Hoping ("hope" :<: ty' :=>: ty)


The |ECompute| command computes the solution to a problem, given its type. 

> runElabCompute :: TY -> CProb -> ProofState VAL
> runElabCompute ty (ElabRunProb e) = do
>     ty' <- bquoteHere ty
>     _ :=>: ptv <- make' Waiting ("ElabRunProb" :<: ty' :=>: ty)
>     goIn
>     mtm <- runElab e
>     case mtm of
>         Just (tm :=>: _)  -> return . valueOf =<< give tm
>         Nothing           -> return ptv
> runElabCompute ty (ResolveProb rn) = do
>     (ref, as, ms) <- elabResolve rn
>     (tm :<: ty) <- inferHere (P ref $:$ as)
>     return (PAIR ty tm)


> runElabElab :: TY -> Loc -> EProb -> ProofState (Elab VAL)
> runElabElab ty loc (ElabProb tm)       = return (makeElab loc (ty :>: tm))
> runElabElab ty loc (ElabInferProb tm)  = return (makeElabInfer loc tm)


> elabEnsure :: VAL -> (Can VAL :>: Can ()) -> Elab (Can VAL, VAL)
> elabEnsure (C v) (ty :>: t) = case halfZip v t of
>     Nothing  -> throwError' $ err "elabEnsure: failed to match!"
>     Just _   -> return (v, pval refl $$ A (C ty) $$ A (C v))
> elabEnsure nv (ty :>: t) = do
>     vu <- unWrapElab $ canTy chev (ty :>: t)
>     let v = fmap valueOf vu
>     p <- EHope (PRF (EQBLUE (C ty :>: nv) (C ty :>: C v))) Bale
>     return (v, p)
>  where
>    chev :: (TY :>: ()) -> WrapElab (() :=>: VAL)
>    chev (ty :>: ()) = WrapElab (EHope ty (return . (() :=>:)))

The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration process to its tip.
When the scheduler hits the goal, the elaboration process will restart.

> suspend :: (String :<: INTM :=>: TY) -> Elab VAL -> ProofState (EXTM :=>: VAL)
> suspend (x :<: tt) elab = do
>     r <- make' Waiting (x :<: tt)
>     Just (E ref xn (Girl LETG (es, Unknown utt, nsupply) ms) tm) <- removeDevEntry
>     putDevEntry (E ref xn (Girl LETG (es, UnknownElab utt elab, nsupply) ms) tm)
>     return r


> suspendMe :: Elab VAL -> ProofState (Maybe a)
> suspendMe elab = do
>     Unknown tt <- getDevTip
>     putDevTip (UnknownElab tt elab)
>     return Nothing


The |chevElab| helper function is a checker-evaluator version of |makeElab|
that can be passed to |canTy| and |elimTy|. It creates appropriate subgoals
for each component and continues elaborating.

> chevElab :: Loc -> (TY :>: InDTmRN) -> Elab (() :=>: VAL)
> chevElab loc (ty :>: tm) = ECompute ty (ElabRunProb (makeElab loc (ty :>: tm)))
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
>     makeElab loc (s :>: dScopeTm sc)

> makeElab loc (w :>: DN n) = do
>     yn <- makeElabInfer loc n
>     q <- EHope (PRF (EQBLUE (SET :>: yn $$ Fst) (SET :>: w))) Bale
>     return (coe @@ [yn $$ Fst, w, q, yn $$ Snd])

> makeElab loc (ty :>: tm) = throwError' $ err "makeElab: can't cope with"
>     ++ errTyVal (ty :<: SET) ++ err " :>: " ++ errTm tm 


> makeElabInfer :: Loc -> ExDTmRN -> Elab VAL

> makeElabInfer loc (t ::$ ss) = do
>     tytv <- makeElabHeadInfer loc t
>     (v :<: ty) <- handleArgs (tytv $$ Snd :<: tytv $$ Fst) ss
>     return (PAIR ty v)
>   where
>     handleArgs :: (VAL :<: TY) -> DSpine RelName -> Elab (VAL :<: TY)
>     handleArgs (v :<: ty) [] = return (v :<: ty)
>     handleArgs (v :<: C cty) (a : as) = do
>         (a', ty') <- elimTy (chevElab loc) (v :<: cty) a
>         handleArgs (v $$ fmap valueOf a' :<: ty') as
>     handleArgs (v :<: ty) as = do
>         cty <- ECan ty Bale
>         handleArgs (v :<: C cty) as

> makeElabInfer loc tm = throwError' $ err "makeElabInfer: can't cope with"
>     ++ errTm (DN tm)

> makeElabHeadInfer :: Loc -> DHead RelName -> Elab VAL
> makeElabHeadInfer loc (DP rn) = ECompute sigSetVAL (ResolveProb rn) Bale

> makeElabHeadInfer loc (DType ty) = do
>     tyv <- ECompute SET (ElabRunProb (makeElab loc (SET :>: ty))) Bale
>     return $ PAIR (ARR tyv tyv) (idVAL "typecast")

> makeElabHeadInfer loc tm = throwError' $ err "makeElabHeadInfer: can't cope with"
>     ++ errTm (DN (tm ::$ []))


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


> sigSetTM :: INTM
> sigSetTM = SIGMA SET (idTM "sst")

> sigSetVAL :: VAL
> sigSetVAL = SIGMA SET (idVAL "ssv")


> import -> CochonTactics where
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term> using the Elab monad."