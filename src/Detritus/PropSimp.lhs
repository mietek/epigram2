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