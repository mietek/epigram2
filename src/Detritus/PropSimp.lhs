

The |flattenAnd| function takes a conjunction and splits it into a list of conjuncts.

> flattenAnd :: VAL -> [VAL]
> flattenAnd (AND p q) = flattenAnd p ++ flattenAnd q
> flattenAnd p = [p]


The |proveConjunction| function takes a conjunction and a list of proofs of its
conjuncts, and produces a proof of the conjunction.

> proveConjunction :: VAL -> [VAL] -> VAL
> proveConjunction p qrs = r
>   where
>     (r, []) = help p qrs
>
>     help :: VAL -> [VAL] -> (VAL, [VAL])
>     help (AND p q) qrs = let
>         (x, qrs')   = help p qrs
>         (y, qrs'')  = help q qrs'
>       in (PAIR x y, qrs'')
>     help _ (qr:qrs) = (qr, qrs)

The |curryProp| function takes a conjunction and a consequent, and produces a
curried proposition that has the pieces of the conjunction as individual
antecedents, followed by the given consequent. Thus
|curryProp (A && B && C) D == (A => B => C => D)|.

> curryProp :: VAL -> VAL -> VAL
> curryProp ps q = curryList $ flattenAnd (AND ps q)
>   where
>     curryList :: [VAL] -> VAL
>     curryList [p] = p
>     curryList (p:ps) = ALL (PRF p) (L (HF "__curry" (\v -> curryList ps))) 


The |curryArg| function takes a proof of a conjunction |P|, and produces a spine
of arguments suitable to apply to a proof of type |curryProp P _|.

> curryArg :: VAL -> [Elim VAL]
> curryArg (PAIR a b) = curryArg a ++ curryArg b
> curryArg a = [A a]


The |uncurryProp| function takes a conjunction |P| and a function |f|. It produces
a function that accepts arguments in a curried style (as required by |curryProp P _|)
and uncurries them to produce a proof of |P|, which it passes to |f|. Thus
|uncurryProp ((A && B) && (C && D)) f == \ w x y z -> f [[w , x] , [y , z]|.

You are not expected to understand this.

> uncurryProp :: VAL -> (VAL -> VAL) -> VAL
> uncurryProp (AND p q) f = uncurryProp p (\v -> uncurryProp q (f . PAIR v))
> uncurryProp _ f = L (HF "__uncurry" f)







> propSimplifyHere :: ProofState ()
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     case propSimplify p of
>         SimplifyBy f    -> f
>         SimplifyNone    -> return ()
>         SimplifyAbsurd  -> throwError' "propSimplifyHere: oh no, goal is absurd!"
                    

> propSimplify :: VAL -> Simplify
> propSimplify ABSURD     = SimplifyAbsurd
> propSimplify TRIVIAL    = SimplifyBy (give VOID >> return ())
> propSimplify (AND p q)  = SimplifyNone {- (| (propSimplify p) ++ (propSimplify q) |)-}
> propSimplify (ALL (PRF p) q) =
>     case propSimplify p of
>         SimplifyAbsurd -> SimplifyBy (do
>             nonsense <- lambdaBoy "__absurd"
>             (ty :=>: _) <- getHoleGoal
>             give (N (nEOp :@ [NP nonsense, ty]))
>             return ()
>           )
>         _ -> SimplifyNone
> propSimplify tm         = SimplifyNone





> propSimplifyHere :: ProofState ()
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     case propSimplify p of
>         SimplifyTo [] [] prf  -> do
>             prf' <- bquoteHere prf
>             equiv <- bquoteHere (coe @@ [PRF TRIVIAL, PRF p,
>                                     CON (PAIR prf (L (K VOID))), VOID])
>             proofTrace . unlines $ ["Simplified to triviality with proof",
>                                     show prf', "yielding equivalence", show equiv]
>             give equiv
>             return ()
>         SimplifyTo qs prfPtoQs prf  -> do
>             let q = PRF (conjunct qs)
>             q' <- bquoteHere q
>             prf' <- bquoteHere prf
>             x <- pickName "q" ""
>             qr <- make (x :<: q')
>             let prfPtoQ = L (HF "__p" (\v -> foldr1 PAIR (map ($$ A v) prfPtoQs)))
>             equiv <- bquoteHere (coe @@ [q, PRF p, CON (PAIR prf prfPtoQ), evTm qr])
>             proofTrace . unlines $ ["Simplified to", show q', "with proof",
>                                     show prf', "yielding equivalence", show equiv]
>             give equiv
>             return ()
>         SimplifyNone      -> throwError' "propSimplifyHere: cannot simplify."
>         SimplifyAbsurd _  -> throwError' "propSimplifyHere: oh no, goal is absurd!"
                    

> conjunct :: [VAL] -> VAL
> conjunct [] = TRIVIAL
> conjunct qs = foldr1 AND qs

> propSimplify :: VAL -> Simplify
> propSimplify ABSURD     = SimplifyAbsurd (L (HF "__absurd" id))
> propSimplify TRIVIAL    = SimplifyTo [] [] (L (HF "__trivial" id))
> propSimplify (AND p q)  = case (propSimplify p, propSimplify q) of
>     (SimplifyAbsurd prf, _) -> SimplifyAbsurd (L (HF "__absurd" (\v -> v $$ Fst)))
>     (_, SimplifyAbsurd prf) -> SimplifyAbsurd (L (HF "__absurd" (\v -> v $$ Snd)))
>     (SimplifyTo rs prfPRs prfRsP, SimplifyTo ss prfQSs prfSsQ) ->
>         SimplifyTo (rs ++ ss)
>             (map (\x -> L (HF "__pq " (\pq -> x $$ A (pq $$ Fst)))) prfPRs ++
>             map (\x -> L (HF "__pq " (\pq -> x $$ A (pq $$ Snd)))) prfQSs)
>             (PAIR prfRsP prfSsQ)
>     _ -> SimplifyNone
> propSimplify (ALL (PRF p) q) =
>     case propSimplify p of
>         SimplifyAbsurd prf -> SimplifyTo [] []
>             (L (K (L (HF "__p" (\v -> nEOp @@ [prf $$ A v, PRF (q $$ A v)])))))
>         _ -> SimplifyNone
> propSimplify tm         = SimplifyNone




         Simply rgs rh -> freshRef ("__propSimp" :<: PRF r) (\ref -> do
>             simpS <- propSimplify (delta <+> rgs :< ref) (s $$ A (NP ref))
>             case (simpR, simpS) of
>                 (SimplyTrivial prfR, Simply qgs h) -> 
>                     return (Simply 
>                        (\tv -> L (K (prfTS tv)))
>                        (\pv -> prfST (prfR pv))) 
>


>             (SimplifyTo _ q prfQR prfRQ, SimplyAbsurd _ prf _) -> return (SimplifyTo
>                     p
>                     (curryProp q ABSURD)
>                     (\qsv ->
>                         L (HF "__r" (\r ->
>                             magic (PRF (s $$ A r))
>                                 (foldl ($$) qsv (curryArg (prfRQ r))))))
>                     (\pv ->
>                       uncurryProp q (\qv -> prf (pv $$ A (prfQR qv)))))
>
>             (_, SimplyTrivial _ prfS _) -> return (simplifyTrivial p (const (L (K (prfS VOID)))))
>
>             _ -> return (simplifyNone p)
>       )

> propSimplify p@(EQBLUE (sty :>: s) (tty :>: t))
>   | not (isNeutral s || isNeutral t) = return (SimplifyTo p
>         (eqGreen @@ [sty, s, tty, t])
>         (\egv -> CON egv)
>         (\ebv -> ebv $$ Out))
>   where
>     isNeutral :: VAL -> Bool
>     isNeutral (N _)  = True
>     isNeutral _      = False 





\begin{enumerate}
\item Discharge the antecedents |sqs| over each conjunct in the consequent to produce a
      conjunction |pqs|.
\item Construct the proofs |pg : p -> pq| from the |tgs| thus:
      \begin{enumerate}
        \item Declare |pref| to be a reference of type |(x : s) => t|.
        \item Apply |pref| to the proof of |s| in the context |delta <+> sqs|, giving a value
              of type |t|, to which |tg| can be applied to produce a proof of |tq|.
        \item Discharge the proof of |tq| over the |sqs| to produce a proof of |pq|.
        \item Discharge |pref| to produce the required proof.
      \end{enumerate}
\item Construct the proof |ph| of |p| in the context |pqs| thus:
      \begin{enumerate}
        \item Declare |sref| to be a reference of type |s|.
        \item Discharge the proof |th| of |t| over the conjuncts |tqs| to produce |th'|.
        \item Let |sgSpine| be the spine of |sgs| applied to |sref| to produce proofs of the |sqs|.
        \item Apply |th'| to each proof of a |tq| (created by applying a |pq| to the |sgSpine|),
              to produce |th''|.
        \item Discharge |th''| over the |sqs| to give a function |th'''| from proofs of the |sqs|
              to proofs of |t|.
        \item Apply |th'''| to the |sgSpine| and discharge |sref| to produce a function |ph| that,
              given a proof of |s|, yields a proof of |t|.
      \end{enumerate}
\end{enumerate}



> problemSimplify :: ProofState ()
> problemSimplify = do
>     lams <- many (pickName "h" "" >>= lambdaBoy)
>     simplifyHypotheses
>     _ :=>: ty <- getHoleGoal
>     (refs, sol) <- simplifyGoal "" ty
>     proofTrace ("refs: " ++ show refs)
>     subgoals <- dischargeTelescope refs
>     proofTrace ("subgoals: " ++ show subgoals)
>     sol' <- dischargeLots refs sol
>     sol'' <- bquoteHere (sol' $$$ fmap (A . valueOf) subgoals)
>     give' sol''
>     return ()


> dischargeTelescope :: Bwd REF -> ProofState (Bwd (EXTM :=>: VAL))
> dischargeTelescope B0 = return B0
> dischargeTelescope (refs :< ref) = do
>     ref' <- dischargeRefPis refs ref
>     subgoal <- makeSubgoal ref'
>     subgoals <- dischargeTelescope refs
>     return (subgoals :< subgoal)


> simplifyHypotheses :: ProofState ()
> simplifyHypotheses = return ()

> simplifyGoal :: String -> TY -> ProofState (Bwd REF, VAL)
> simplifyGoal _ UNIT = return (B0, VOID)
> simplifyGoal _ (SIGMA s t) = do
>     (sRefs, sVal) <- simplifyGoal (fortran t) s
>     (tRefs, tVal) <- simplifyGoal "" (t $$ A sVal)
>     --tVal' <- dischargeLots tRefs tVal
>     --tRefs' <- mapM (dischargeRefPis sRefs) tRefs
>     --let tVal'' = tVal' $$$ fmap (\tref -> A (NP tref $$$ fmap (A . NP) sRefs)) tRefs'
>     return (sRefs <+> tRefs, PAIR sVal tVal)
> simplifyGoal _ (PRF p) = do
>     nsupply <- askNSupply
>     case runReaderT (propSimplify B0 p) nsupply of
>         Nothing                   -> cannotSimplify "" (PRF p)
>         Just (SimplyAbsurd _)     -> throwError' "simlpifyGoal: oh no, goal is absurd!"
>         Just (Simply qs _ h)      -> return (qs, h)





> problemSimplify :: ProofState (EXTM :=>: VAL)
> problemSimplify = simplifyGoal'

> simplifyGoal' :: ProofState (EXTM :=>: VAL)
> simplifyGoal' = getHoleGoal >>= simplifyGoal . valueOf



> simplifyHypothesis :: TY -> ProofState Simplify

> simplifyHypothesis UNIT = return (SimplyTrivial VOID)

> simplifyHypothesis (SIGMA s t) = do
>     sSimp <- simplifyHypothesis s
>     case sSimp of
>         SimplyAbsurd prf -> return (SimplyAbsurd (prf . ($$ Fst)))
>         Simply srefs sbits sv -> do
>             tSimp <- simplifyHypothesis (t $$ A sv)
>             case tSimp of
>                 SimplyAbsurd prf -> return (SimplyAbsurd (prf . ($$ Snd)))
>                 Simply trefs tbits tv ->
>                     return (Simply
>                         (srefs <+> trefs)
>                         (fmap (..! ($$ Fst)) sbits
>                             <+> fmap (..! ($$ Snd)) tbits) 
>                         (PAIR sv tv))

> simplifyHypothesis (PRF p) = do
>     nsupply <- askNSupply
>     es <- getBoysBwd
>     let Just s = runReaderT (forceSimplify es B0 p) nsupply
>     return s

> simplifyHypothesis ty = simplifyNone "" ty



> simplifyGoal :: TY -> ProofState (EXTM :=>: VAL)

> simplifyGoal (PI s t) = do
>     sSimp <- simplifyHypothesis s
>     case sSimp of
>         SimplyAbsurd prf -> do
>             ff <- bquoteHere (L (HF "ff" (\sv ->
>                                             magic (t $$ A sv) (prf sv))))
>             give ff
>         Simply srefs bits sv -> do
>             st <- dischargePiLots srefs (t $$ A sv)
>             st' <- bquoteHere st
>             make ("" :<: st')
>             goIn
>             Data.Traversable.mapM (const (lambdaBoy (fortran t))) srefs
>             _ :=>: tv <- simplifyGoal'
>             freshRef ("s" :<: s) (\sref -> do
>                 let v = tv $$$ fmap (A . ($$ A NP sref)) bits
>                 v' <- bquote (B0 :< sref) v
>                 give (L (fortran t :. v'))
>               )

> simplifyGoal UNIT = give VOID
> simplifyGoal (SIGMA s t) = do
>     stm <- bquoteHere s
>     make (fortran t :<: stm)
>     goIn
>     stm' :=>: sv <- simplifyGoal s
>     let t' = t $$ A sv
>     ttm <- bquoteHere t'
>     make ("" :<: ttm)
>     goIn
>     ttm' :=>: tv <- simplifyGoal t'
>     give (PAIR (N stm') (N ttm'))

> simplifyGoal (PRF p) = do
>     optional propSimplifyHere
>     getMotherDefinition <* goOut

> simplifyGoal _ = getMotherDefinition <* goOut