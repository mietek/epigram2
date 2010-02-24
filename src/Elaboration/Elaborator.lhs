%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Elaboration.Elaborator where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Traversable

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features ()

> import ProofState.Developments
> import ProofState.ElabMonad
> import ProofState.Lifting
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import Tactics.PropSimp

> import Elaboration.Unification

> import Cochon.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


\section{Implementing the |Elab| monad}
\label{sec:elab_monad}

The |runElab| proof state command actually interprets an |Elab x| in
the proof state. That is, it defines the semantics of the |Elab| syntax.

> runElab :: Bool -> (TY :>: Elab (INTM :=>: VAL))
>                       -> ProofState (INTM :=>: VAL, Bool)
> runElab _ (_ :>: Bale x) = return (x, True)

> runElab True (ty :>: ELambda x f) = case lambdable ty of
>     Just (_, s, tyf) -> do
>         ref <- lambdaBoy x
>         runElab True (tyf (NP ref) :>: f ref)
>     Nothing -> throwError' $ err "runElab: type" ++ errTyVal (ty :<: SET)
>                                  ++ err "is not lambdable!"

> runElab False (ty :>: ELambda s f) = runElabTop (ty :>: ELambda s f)

> runElab top (ty :>: EGoal f) = runElab top (ty :>: f ty)

> runElab top (ty :>: EHope tyHope f) = runElabHope tyHope
>     >>= runElab top . (ty :>:) . f

> runElab top (ty :>: EWait s tyWait f) = do
>     tyWait' <- bquoteHere tyWait
>     tt <- make' Waiting (s :<: tyWait' :=>: tyWait)
>     runElab top (ty :>: f tt)

> runElab top (ty :>: ECompute tyComp p f) = runElabCompute tyComp p
>     >>= runElab top . (ty :>:) . f

> runElab top (ty :>: ESolve ref@(_ := HOLE Hoping :<: _) v f) = do
>     v' <- bquoteHere v
>     tt <- solveHole ref v'
>     runElab top (ty :>: f tt)

>{- runElab top (ty :>: ESolve ref@(_ := DEFN tv :<: rty) v f) = do
>     -- we should check tv == v in some fashion
>     runElab top (ty :>: f tv) -}

> runElab top (ty :>: EElab tyElab (l, p) f)  = runElabElab tyElab l p
>     >>= runElab top . (ty :>:) . (>>= f)

> runElab top (ty :>: ECan (C c) f) = runElab top (ty :>: f c)
> runElab True (ty :>: ECan tm f) = do
>     t :=>: tv <- suspendMe (ECan tm f)
>     return (N t :=>: tv, False)
> runElab False (ty :>: ECan tm f) = do
>     ty' <- bquoteHere ty
>     t :=>: tv <- suspend ("can" :<: ty' :=>: ty) (ECan tm f)
>     return (N t :=>: tv, False)

> runElab True (ty :>: ECry e)            = do
>     e' <- distillErrors e
>     throwError e'

<     let msg = show (prettyStackError e')
<     putHoleKind (Crying msg)
<     t :=>: tv <- getMotherDefinition
<     return (N t :=>: tv, False)

> runElab False (ty :>: ECry e) = runElabTop (ty :>: ECry e)

> runElab True (ty :>: EFake b f)           = do
>     GirlMother (nom := HOLE _ :<: ty) _ _ _ <- getMother
>     let fr = nom := FAKE :<: ty
>     xs <- if b  then  (| boySpine getAuncles |)
>                 else  (| (init . boySpine) getAuncles |)
>     let tm = P fr $:$ xs
>     runElab True . (ty :>:) . f $ tm :=>: evTm tm

> runElab False (ty :>: EFake b f) = runElabTop (ty :>: EFake b f)


> runElab top (ty :>: EResolve rn f) = do
>     (ref, as, ms) <- elabResolve rn
>     let tm = P ref $:$ as
>     (tmv :<: tyv) <- inferHere tm
>     tyv'  <- bquoteHere tyv
>     runElab top (ty :>: f (PAIR tyv' (N tm) :=>: PAIR tyv tmv, ms))
>   

> runElab top (ty :>: EQuote v f) = do
>     tm <- bquoteHere v
>     runElab top (ty :>: f (tm :=>: v))

> runElab top (ty :>: ECoerce (_S :=>: _Sv) (_T :=>: _Tv) (s :=>: sv) f) = do
>     eq <- withNSupply (equal $ SET :>: (_Sv, _Tv))
>     tt <- if eq
>         then return (s :=>: sv)
>         else do
>             q :=>: qv <- runElabHope (PRF (EQBLUE (SET :>: _Sv) (SET :>: _Tv)))
>             return $ N (coe :@ [_S, _T, q, s]) :=>: coe @@ [_Sv, _Tv, qv, sv]
>     runElab top (ty :>: f tt)

> runElab top (ty :>: tm) = throwError' . err $ "runElab: cannot evaluate "
>                                                 ++ show tm

> runElabTop :: (TY :>: Elab (INTM :=>: VAL)) -> ProofState (INTM :=>: VAL, Bool)
> runElabTop (ty :>: elab) = do
>     ty' <- bquoteHere ty
>     x <- pickName "h" ""
>     make' Waiting (x :<: ty' :=>: ty)
>     goIn
>     (tm :=>: tmv, okay) <- runElab True (ty :>: elab)
>     if okay
>         then  return . (, True)  =<< neutralise =<< give tm
>         else  return . (, False) =<< neutralise =<< getMotherDefinition


The |EHope| command hopes for an element of a given type. If it is asking for a
proof, we might be able to find one, but otherwise we just create a hole.

> runElabHope :: TY -> ProofState (INTM :=>: VAL)
> runElabHope (PRF p)  = hopeProof p <|> lastHope (PRF p)
> runElabHope ty       = lastHope ty

> lastHope :: TY -> ProofState (INTM :=>: VAL)
> lastHope ty = do
>     ty' <- bquoteHere ty
>     neutralise =<< make' Hoping ("hope" :<: ty' :=>: ty)


> hopeProof :: VAL -> ProofState (INTM :=>: VAL)

> hopeProof p@(EQBLUE (_S :>: s) (_T :>: (NP ref@(_ := HOLE Hoping :<: _)))) = do
>     p' <- bquoteHere p
>     neutralise =<< suspend ("hope" :<: PRF p' :=>: PRF p)
>         (ESolve ref s . const $ EQuote (pval refl $$ A _S $$ A s) Bale)

> hopeProof p@(EQBLUE (_T :>: (NP ref@(_ := HOLE Hoping :<: _))) (_S :>: s)) = do
>     p' <- bquoteHere p
>     neutralise =<< suspend ("hope" :<: PRF p' :=>: PRF p)
>         (ESolve ref s . const $ EQuote (pval refl $$ A _S $$ A s) Bale)

> hopeProof p = do
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Just (SimplyTrivial prf) -> do
>             prf' <- bquoteHere prf
>             return $ prf' :=>: prf
>         Just (SimplyAbsurd _) -> do
>             throwError' $ err "hopeProof: proposition is absurd!"
>         Just (Simply qs _ h) -> do
>             qrs <- Data.Traversable.mapM (runElabHope . pty) qs
>             h' <- dischargeLots qs h
>             let prf = h' $$$ fmap (A . valueOf) qrs
>             prf' <- bquoteHere prf
>             return $ prf' :=>: prf
>         Nothing -> (|)
>         


The |ECompute| command computes the solution to a problem, given its type. 

> runElabCompute :: TY -> CProb -> ProofState (INTM :=>: VAL)
> runElabCompute ty (SubProb elab) =
>     return . fst =<< runElab False (ty :>: elab)

> runElabElab :: TY -> Loc -> EProb -> ProofState (Elab (INTM :=>: VAL))
> runElabElab ty loc (ElabProb tm)       = return (makeElab loc (ty :>: tm))
> runElabElab ty loc (ElabInferProb tm)  = return (makeElabInfer loc tm)


> {- elabEnsure :: VAL -> (Can VAL :>: Can ()) -> Elab (Can VAL, VAL)
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
>    chev (ty :>: ()) = WrapElab (EHope ty (return . (() :=>:))) -}

The |suspend| command can be used to delay elaboration, by creating a subgoal
of the given type and attaching a suspended elaboration process to its tip.
When the scheduler hits the goal, the elaboration process will restart.

> suspend :: (String :<: INTM :=>: TY) -> Elab(INTM :=>: VAL)
>                -> ProofState (EXTM :=>: VAL)
> suspend (x :<: tt) elab = do
>     r <- make' Waiting (x :<: tt)
>     Just (E ref xn (Girl LETG (es, Unknown utt, nsupply) ms) tm) <- removeDevEntry
>     putDevEntry (E ref xn (Girl LETG (es, UnknownElab utt elab, nsupply) ms) tm)
>     return r


> suspendMe :: Elab (INTM :=>: VAL) -> ProofState (EXTM :=>: VAL)
> suspendMe elab = do
>     Unknown tt <- getDevTip
>     putDevTip (UnknownElab tt elab)
>     getMotherDefinition


\section{Elaboration}
\label{sec:elaborator}

\subsection{Elaborating |INDTM|s}

The |elaborate| command elaborates a term in display syntax, given its type,
to produce an elaborated term and its value representation. It behaves
similarly to |check| from subsection~\ref{subsec:type-checking}, except that
it operates in the |Elab| monad, so it can create subgoals and
$\lambda$-lift terms.

> elaborate :: Loc -> (TY :>: InDTmRN) -> ProofState (INTM :=>: VAL)
> elaborate loc (ty :>: tm) = runElab False (ty :>: makeElab loc (ty :>: tm))
>     >>= return . fst

> elaborate' = elaborate (Loc 0)

> elaborateHere :: Loc -> InDTmRN -> ProofState (INTM :=>: VAL)
> elaborateHere loc tm = do
>     _ :=>: ty <- getHoleGoal
>     return . fst =<< runElab True (ty :>: makeElab loc (ty :>: tm))

> elaborateHere' = elaborateHere (Loc 0)

> elabInfer :: Loc -> ExDTmRN -> ProofState (INTM :=>: VAL :<: TY)
> elabInfer loc tm = do
>     (tt, _) <- runElab False (sigSetVAL :>: makeElabInfer loc tm)
>     let (tt' :<: _ :=>: ty) = extractNeutral tt
>     return (tt' :<: ty)

> elabInfer' = elabInfer (Loc 0)



> subElab :: Loc -> (TY :>: InDTmRN) -> Elab (INTM :=>: VAL)
> subElab loc (ty :>: tm) = ECompute ty (SubProb (makeElab loc (ty :>: tm))) Bale


> makeElab :: Loc -> (TY :>: InDTmRN) -> Elab (INTM :=>: VAL)

> import <- MakeElabRules

These rules should be moved to features.

> makeElab loc (SET :>: DIMU Nothing iI d i) = do
>       l :=>: lv <- EFake False Bale
>       iI :=>: iIv <- subElab loc (SET :>: iI)
>       d :=>: dv <- subElab loc (ARR iIv (IDESC iIv) :>: d)
>       i :=>: iv <- subElab loc (iIv :>: i)

<       lastIsIndex <- withNSupply (equal (SET :>: (iv,N (P (last xs)))))
<       guard lastIsIndex
<       -- should check i doesn't appear in d (fairly safe it's not in iI :))

>       return $ IMU (Just (N l)) iI d i :=>: IMU (Just lv) iIv dv iv

> makeElab loc (PI UNIT t :>: DCON f) = do
>     tm :=>: tmv <- subElab loc (t $$ A VOID :>: f)
>     return $ LK tm :=>: LK tmv

> makeElab loc (PI (MU l d) t :>: DCON f) = do
>     _ :=>: tmv <- subElab loc $ case l of
>         Nothing  -> elimOpMethodType $$ A d $$ A t :>: f
>         Just l   -> elimOpLabMethodType $$ A l $$ A d $$ A t :>: f
>     x <- ELambda (fortran t) Bale
>     EQuote (elimOp @@ [d, NP x, t, tmv]) Bale

> makeElab loc (PI (SIGMA d r) t :>: DCON f) = do
>     let mt =  PI d . L . HF (fortran r) $ \ a ->
>               PI (r $$ A a) . L . HF (fortran t) $ \ b ->
>               t $$ A (PAIR a b)
>     mt' :=>: _ <- EQuote mt Bale
>     tm :=>: tmv <- subElab loc (mt :>: f)
>     x <- ELambda (fortran t) Bale
>     return $ N ((tm :? mt') :$ A (N (P x :$ Fst)) :$ A (N (P x :$ Snd)))
>                     :=>: tmv $$ A (NP x $$ Fst) $$ A (NP x $$ Snd)

> makeElab loc (PI (ENUMT e) t :>: m) | isTuply m = do
>     _ :=>: tmv <- subElab loc (branchesOp @@ [e, t] :>: m)
>     x <- ELambda (fortran t) Bale
>     EQuote (switchOp @@ [e, NP x, t, tmv]) Bale
>   where
>     isTuply :: InDTmRN -> Bool
>     isTuply DVOID        = True
>     isTuply (DPAIR _ _)  = True
>     isTuply _            = False

> makeElab loc (MONAD d x :>: DCON t) = makeElab loc (MONAD d x :>: DCOMPOSITE t)
> makeElab loc (QUOTIENT a r p :>: DPAIR x DVOID) =
>   makeElab loc (QUOTIENT a r p :>: DCLASS x)

> makeElab loc (NU d :>: DCOIT DU sty f s) = do
>   d' :=>: _ <- EQuote d Bale
>   makeElab loc (NU d :>: DCOIT (DTIN d') sty f s)



We use underscores |DU| in elaboration to mean "figure this out yourself".

> makeElab loc (ty :>: DU) = EHope ty Bale
> makeElab loc (ty :>: DQ s) = EWait s ty neutralise


Elaborating a canonical term with canonical type is a job for |canTy|.

> makeElab loc (C ty :>: DC tm) = do
>     v <- canTy (subElab loc) (ty :>: tm)
>     return $ (C $ fmap termOf v) :=>: (C $ fmap valueOf v)


There are a few possibilities for elaborating $\lambda$-abstractions. If both the
range and term are constants, then we simply |makeElab| underneath. This avoids
creating some trivial children. 

> makeElab loc (PI s (L (K t)) :>: DL (DK dtm)) = do
>     tm :=>: tmv <- subElab loc (t :>: dtm)
>     return $ LK tm :=>: LK tmv

Otherwise, we can simply create a |lambdaBoy| in the current
development, and carry on elaborating.

> makeElab loc (ty :>: DL sc) = do
>     ref <- ELambda (dfortran (DL sc)) Bale
>     ty' <- EGoal Bale
>     makeElab loc (ty' :>: dScopeTm sc)


We push types in to neutral terms by calling |makeElabInfer| on the term, then
coercing the result to the required type. (Note that |ECoerce| will check if the
types are equal, and if so it will not insert a redundant coercion.)

> makeElab loc (w :>: DN n) = do
>     tt <- makeElabInfer loc n
>     let (yt :=>: yn :<: ty :=>: tyv) = extractNeutral tt
>     w' :=>: _ <- EQuote w Bale
>     ECoerce (ty :=>: tyv) (w' :=>: w) (yt :=>: yn) Bale


If we already have an evidence term, we just have to type-check it.

> makeElab loc (ty :>: DTIN tm) = do
>     let nsupply = (B0 :< ("__makeElabDTIN", 0), 0) :: NameSupply
>     case liftError (typeCheck (check (ty :>: tm)) nsupply) of
>         Left e -> throwError e
>         Right tt -> return tt


If nothing else matches, give up and report an error.

> makeElab loc (ty :>: tm) = throwError' $ err "makeElab: can't push"
>     ++ errTyVal (ty :<: SET) ++ err "into" ++ errTm tm 


\subsection{Elaborating |EXDTM|s}

The |makeElabInfer| command is to |infer| in subsection~\ref{subsec:type-inference} 
as |elaborate| is to |check|. It infers the type of a display term, calling on
the elaborator rather than the type-checker.

> extractNeutral :: INTM :=>: VAL -> INTM :=>: VAL :<: INTM :=>: TY
> extractNeutral (PAIR ty tm :=>: tv) = tm :=>: tv $$ Snd :<: ty :=>: tv $$ Fst
> extractNeutral (tm :=>: tv) = N (tm' :$ Snd) :=>: tv $$ Snd :<: N (tm' :$ Fst) :=>: tv $$ Fst
>   where tm' = tm :? sigSetTM

> makeElabInfer :: Loc -> ExDTmRN -> Elab (INTM :=>: VAL)

> makeElabInfer loc (t ::$ ss) = do
>     tt <- makeElabInferHead loc t
>     let (tm :=>: tmv :<: ty :=>: tyv) = extractNeutral tt
>     let ss' = {-case ms of
>                   Just sch  -> schemer sch ss
>                   Nothing   -> -} ss
>     (t :=>: v :<: y) <- handleArgs (tm :? ty :=>: tmv :<: tyv) ss'
>     y' :=>: _ <- EQuote y Bale
>     return $ PAIR y' (N t) :=>: PAIR y v
>   where
>     schemer :: Scheme INTM -> DSpine RelName -> DSpine RelName
>     schemer (SchType _) as = as
>     schemer (SchImplicitPi (x :<: s) schT) as =
>         A DU : schemer schT as
>     schemer (SchExplicitPi (x :<: schS) schT) (a:as) =
>         a : schemer schT as
>     schemer (SchExplicitPi (x :<: schS) schT) [] = []

>     handleArgs :: (EXTM :=>: VAL :<: TY) -> DSpine RelName -> Elab (EXTM :=>: VAL :<: TY)
>     handleArgs (tt :<: ty) [] = return (tt :<: ty)
>     handleArgs (t :=>: v :<: C cty) (a : as) = do
>         (a', ty') <- elimTy (subElab loc) (v :<: cty) a
>         handleArgs (t :$ fmap termOf a' :=>: v $$ fmap valueOf a' :<: ty') as
>     handleArgs (tt :<: ty) as = do
>         cty <- ECan ty Bale
>         handleArgs (tt :<: C cty) as

> makeElabInferHead :: Loc -> DHead RelName -> Elab (INTM :=>: VAL)

> makeElabInferHead loc (DP rn) = do
>     (tm :=>: tmv, ms) <- EResolve rn Bale
>     return $ tm :=>: tmv

> makeElabInferHead loc (DType ty) = do
>     tm :=>: tmv <- subElab loc (SET :>: ty)
>     return $ PAIR (ARR tm tm) (idTM "typecast")
>                  :=>: PAIR (ARR tmv tmv) (idVAL "typecast")

> makeElabInferHead loc tm = throwError' $ err "makeElabInferHead: can't cope with"
>     ++ errTm (DN (tm ::$ []))


> neutraliseElab :: Elab (EXTM :=>: VAL) -> Elab (INTM :=>: VAL)
> neutraliseElab f = do
>     tm :=>: tmv <- f
>     return (N tm :=>: tmv)

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
>             (tm :=>: tmv, okay) <- runElab True (valueOf tt :>: elab)
>             if okay
>                 then give' tm >> return ()
>                 else proofTrace "scheduler: elaboration suspended."
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



The |elabResolve| command resolves a relative name to a reference,
a spine of shared parameters to which it should be applied, and
possibly a scheme. If the name ends with "./", the scheme will be
discarded, so all parameters can be provided explicitly.
\question{What should the syntax be for this, and where should it be handled?}

> elabResolve :: RelName -> ProofState (REF, Spine {TT} REF, Maybe (Scheme INTM))
> elabResolve x = do
>     pc <- get
>     let  x'    = if fst (last x) == "/" then init x else x
>          uess  = inBScope pc
>     ans@(r, s, ms) <- resolve x' (Just $ uess) (inBFScope uess)  
>        `catchEither` (err $ "elabResolve: cannot resolve name: " ++ showRelName x')
>     if fst (last x) == "/" then return (r, s, Nothing) else return ans


\subsection{Elaborated Construction Commands}


The |elabGive| command elaborates the given display term in the appropriate type for
the current goal, and calls the |give| command on the resulting term. If its argument
is a nameless question mark, it avoids creating a pointless subgoal by simply returning
a reference to the current goal (applied to the appropriate shared parameters).

> elabGive :: InDTmRN -> ProofState (EXTM :=>: VAL)
> elabGive tm = elabGive' tm <* goOut

> elabGiveNext :: InDTmRN -> ProofState (EXTM :=>: VAL)
> elabGiveNext tm = elabGive' tm <* (nextGoal <|> goOut)

> elabGive' :: InDTmRN -> ProofState (EXTM :=>: VAL)
> elabGive' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown _ -> do
>             case tm of
>                 DQ "" -> do
>                     GirlMother ref _ _ _ <- getMother
>                     aus <- getGreatAuncles
>                     return (applyAuncles ref aus)
>                 _ -> do
>                     tm' :=>: _ <- elaborateHere' tm
>                     give' tm'
>         _  -> throwError' $ err "elabGive: only possible for incomplete goals."


The |elabMake| command elaborates the given display term in a module to
produce a type, then converts the module to a goal with that type. Thus any
subgoals produced by elaboration will be children of the resulting goal.

> elabMake :: (String :<: InDTmRN) -> ProofState (EXTM :=>: VAL)
> elabMake (s :<: ty) = do
>     makeModule s
>     goIn
>     ty' :=>: _ <- elaborate' (SET :>: ty)
>     tm <- moduleToGoal ty'
>     goOutProperly
>     return tm


The |elabProgram| command adds a label to a type, given a list of arguments.
e.g. with a goal |plus : Nat -> Nat -> Nat|, |program x,y| will give a proof
state of:

\begin{verbatim}
plus [
  plus := ? : (x : Nat) -> (y : Nat) -> <plus x y : Nat>
  \ x : Nat
  \ y : Nat
] plus x y call : Nat
\end{verbatim}

> elabProgram :: [String] -> ProofState (EXTM :=>: VAL)
> elabProgram args = do
>     n <- getMotherName
>     (_ :=>: g) <- getHoleGoal
>     let pn = P (n := FAKE :<: g)
>     let newty = pity (mkTel pn g [] args)
>     newty' <- bquoteHere newty
>     g :=>: _ <- make (fst (last n) :<: newty') 
>     argrefs <- traverse lambdaBoy args
>     let fcall = pn $## (map NP argrefs) 
>     let call = g $## (map NP argrefs) :$ Call (N fcall)
>     r <- give' (N call)
>     goIn
>     return r
>   where mkTel :: NEU -> TY -> [VAL] -> [String] -> TEL TY
>         mkTel n (PI s t) args (x:xs)
>            = (x :<: s) :-: (\val -> mkTel n (t $$ A val) (val:args) xs)
>         mkTel n r args _ = Target (LABEL (mkL n (reverse args)) r)
>         
>         mkL :: NEU -> [VAL] -> VAL
>         mkL n [] = N n
>         mkL n (x:xs) = mkL (n :$ (A x)) xs


The |elabPiBoy| command elaborates the given display term to produce a type, and
creates a $\Pi$-boy with that type.

> elabPiBoy :: (String :<: InDTmRN) -> ProofState REF
> elabPiBoy (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     piBoy' (s :<: tt)

> elabLamBoy :: (String :<: InDTmRN) -> ProofState REF
> elabLamBoy (s :<: ty) = do
>     tt <- elaborate' (SET :>: ty)
>     lambdaBoy' (s :<: tt)


\subsection{Elaborating Schemes}

> elabLet :: (String :<: Scheme InDTmRN) -> ProofState (EXTM :=>: VAL)
> elabLet (x :<: sch) = do
>     makeModule x
>     goIn
>     make ("tau" :<: SET)
>     goIn
>     (sch', ty :=>: _) <- elabScheme B0 sch
>     moduleToGoal (N ty)     
>     putMotherScheme sch'
>     r <- elabProgram (schemeNames sch')
>     putMotherScheme sch' -- this is wrong but does it matter?
>     return r


> elabScheme :: Entries -> Scheme InDTmRN -> ProofState (Scheme INTM, EXTM :=>: VAL)

> elabScheme es (SchType ty) = do
>     ty' :=>: _ <- elaborate' (SET :>: ty)
>     tt <- give ty'
>     return (SchType (es -| ty'), tt)

> elabScheme es (SchExplicitPi (x :<: s) t) = do
>     make ("tau" :<: SET)
>     goIn
>     (s', ty :=>: _) <- elabScheme es s
>     piBoy (x :<: N ty)
>     e <- getDevEntry
>     (t', tt) <- elabScheme (es :< e) t
>     return (SchExplicitPi (x :<: s') t', tt)

> elabScheme es (SchImplicitPi (x :<: s) t) = do
>     ss <- elaborate' (SET :>: s)
>     piBoy (x :<: termOf ss)
>     e <- getDevEntry
>     (t', tt) <- elabScheme (es :< e) t
>     return (SchImplicitPi (x :<: (es -| termOf ss)) t', tt)




The |resolveHere| command resolves a relative name to a reference,
discarding any shared parameters it should be applied to.

> resolveHere :: RelName -> ProofState REF
> resolveHere x = elabResolve x >>= (\ (r, _, _) -> return r)
