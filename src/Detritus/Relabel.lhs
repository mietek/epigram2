>        {- proofTrace $ "subst: " ++ show subst
>         mapM (\ (ref, val) -> bquoteHere val >>= solveHole ref) subst 
>         let wtm' = fst $ tellNews (map (\ (n := HOLE Hoping :<: ty, val) ->
>                                         (n := DEFN val :<: ty, GoodNews))
>                                         subst) wtm -}

<         (q :=>: qv, True) <- runElabHope False (PRF (EQBLUE (s :>: wv) (s :>: a)))         

<         tm :=>: _ <- mapStateT (either (Left . (fmap $ fmap $ fmap fst)) Right)
<                          (match (s :>: (w, a)))

>     match :: TY :>: (InDTmRN, VAL) -> ProofStateT (InDTmRN, VAL) (INTM :=>: VAL)
>     match (ty :>: (DNP [(x, Rel 0)], a)) =
>         mapStateT (either (Left . error "oh no") Right) $ do
>             ty'  <- bquoteHere ty
>             a'   <- bquoteHere a
>             make (x :<: ty')
>             goIn
>             neutralise =<< give a'
>     match (C cty :>: (DC dc, C cv)) = case halfZip dc cv of
>        Just c   -> do
>            c' <- canTy match (cty :>: c)
>            return $ C (fmap termOf c') :=>: C (fmap valueOf c')
>        Nothing  -> throwError' $ err "relabel: halfzip failed!"