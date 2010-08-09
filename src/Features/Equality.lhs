\section{Equality}
\label{sec:Features.Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Equality where

%endif


> import -> CanConstructors where
>   EqBlue :: (t :>: t) -> (t :>: t) -> Can t

> import -> CanPats where
>   pattern EQBLUE p q = C (EqBlue p q)

> import -> CanTraverse where
>   traverse f (EqBlue (pty :>: p) (qty :>: q)) =
>     (|EqBlue (|(:>:) (f pty) (f p)|) (|(:>:) (f qty) (f q)|)|)

> import -> CanPretty where
>   pretty (EqBlue pp qq) = pretty (DEqBlue (foo pp) (foo qq))
>     where
>       foo :: (DInTmRN :>: DInTmRN) -> DExTmRN
>       foo (_    :>: DN x  ) = x
>       foo (xty  :>: x     ) = DType xty ::$ [A x] 

> import -> CanTyRules where
>   canTy chev (Prop :>: EqBlue (y0 :>: t0) (y1 :>: t1)) = do
>     y0y0v@(y0 :=>: y0v) <- chev (SET :>: y0)
>     t0t0v@(t0 :=>: t0v) <- chev (y0v :>: t0)
>     y1y1v@(y1 :=>: y1v) <- chev (SET :>: y1)
>     t1t1v@(t1 :=>: t1v) <- chev (y1v :>: t1)
>     return $ EqBlue (y0y0v :>: t0t0v) (y1y1v :>: t1t1v)
>   canTy chev (Prf (EQBLUE (y0 :>: t0) (y1 :>: t1)) :>: Con p) = do
>     ppv@(p :=>: pv) <- chev (PRF (eqGreen @@ [y0, t0, y1, t1]) :>: p)
>     return $ Con ppv

> import -> ElimTyRules where
>   elimTy chev (_ :<: Prf (EQBLUE (t0 :>: x0) (t1 :>: x1))) Out =
>     return (Out, PRF (eqGreen @@ [t0 , x0 , t1 , x1]))

> import -> OpCode where
>   eqGreen = Op { opName = "eqGreen"
>                , opArity = 4
>                , opTyTel =  "S" :<: SET :-: \ sS -> "s" :<: sS :-: \ s ->
>                             "T" :<: SET :-: \ tT -> "t" :<: tT :-: \ t ->
>                             Target PROP
>                , opRun = opRunEqGreen
>                , opSimp = \_ _ -> empty
>                } where
>                opty chev [y0,t0,y1,t1] = do
>                    (y0 :=>: y0v) <- chev (SET :>: y0)
>                    (t0 :=>: t0v) <- chev (y0v :>: t0)
>                    (y1 :=>: y1v) <- chev (SET :>: y1)
>                    (t1 :=>: t1v) <- chev (y1v :>: t1)
>                    return ([ y0 :=>: y0v
>                            , t0 :=>: t0v
>                            , y1 :=>: y1v
>                            , t1 :=>: t1v ]
>                           , PROP)
>                opty _  _             = throwError' "eqGreen: invalid arguments."

>   coe = Op { opName = "coe"
>            , opArity = 4
>            , opTyTel =  "S" :<: SET :-: \ sS -> "T" :<: SET :-: \ tT ->
>                         "Q" :<: PRF (EQBLUE (SET :>: sS) (SET :>: tT)) :-: \ _ ->
>                         "s" :<: sS :-: \ _ -> Target tT
>            , opRun = oprun
>            , opSimp = \ [sS, tT, _, s] r -> case s of
>                N s | equal (SET :>: (sS, tT)) r -> pure s
>                _ -> (|)
>            } where
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [_S, _T, q, v] | partialEq _S _T q = Right v
>            oprun [C (Mu t0), C (Mu t1), q, s] = case halfZip (Mu (dropLabel t0)) (Mu (dropLabel t1)) of
>              Nothing -> Right $ nEOp @@ [q $$ Out, C (Mu t1)]
>              Just fxy -> coerce fxy (q $$ Out) s
>            oprun [C x,C y,q,s] = case halfZip x y of
>              Nothing  -> Right $ nEOp @@ [q $$ Out, C y]
>              Just fxy -> coerce fxy (q $$ Out) s
>            oprun [N x,y,q,s] = Left x
>            oprun [x,N y,q,s] = Left y
>            oprun vs = error ("coe: undefined for arguments"
>                                  ++ unlines (map show vs))

>   coh = Op { opName = "coh"
>            , opArity = 4
>            , opTyTel =
>                "S" :<: SET :-: \ _S -> "T" :<: SET :-: \ _T ->
>                "Q" :<: PRF (EQBLUE (SET :>: _S) (SET :>: _T)) :-: \ _Q ->
>                "s" :<: _S :-: \ s -> Target $ PRF $
>                EQBLUE (_S :>: s) (_T :>: (coe @@ [_S, _T, _Q, s]))
>            , opRun = oprun
>            , opSimp = \ [_S, _T, _, s] r ->
>                if equal (SET :>: (_S, _T)) r
>                  then pure $ P refl :$ A _S :$ A s
>                  else (|)
>            } where
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [_S, _T, q, s] | partialEq _S _T q =
>              Right (pval refl $$ A _S $$ A s)
>            oprun [N x,y,q,s] = Left x
>            oprun [x,N y,q,s] = Left y
>            oprun [_S,_T,_Q,s] = Right $
>              pval cohAx $$ A _S $$ A _T $$ A _Q $$ A s
>            oprun vs = error ("coe: undefined for arguments"
>                                  ++ unlines (map show vs))

> import -> Operators where
>   eqGreen :
>   coe :
>   coh :

> import -> RulesCode where
>   cohAx = [("Axiom",0),("coh",0)] := (DECL :<: cohType) where
>     cohType = PRF $ 
>               ALL SET $ L $ "S" :. [._S.
>               ALL SET $ L $ "T" :. [._T.
>               ALL (PRF (EQBLUE (SET :>: NV _S) (SET :>: NV _T)))
>                  $ L $ "Q" :. [._Q.
>               ALL (NV _S) $ L $ "s" :. [.s.
>               EQBLUE (NV _S :>: NV s)
>                      (NV _T :>: N (coe :@ [NV _S, NV _T, NV _Q, NV s]))
>               ]]]]
>   refl = [("Axiom",0),("refl",0)] := (DECL :<: reflType) where
>     reflType = PRF $  ALL SET $ L $ "S" :. [._S.
>                       ALL (NV _S) $ L $ "s" :. [.s.
>                       EQBLUE (NV _S :>: NV s) (NV _S :>: NV s) ]]

>   substEq = [("Primitive", 0), ("substEq", 0)] := DEFN seDef :<: seTy where
>     seTy = PI SET $ L $ "X" :. [._X.
>                PI (NV _X) $ L $ "x" :. [.x.
>                PI (NV _X) $ L $ "y" :. [.y.
>                PI (PRF (EQBLUE (NV _X :>: NV x) (NV _X :>: NV y))) $ L $ "q" :. [.q.
>                PI (ARR (NV _X) SET) $ L $ "P" :. [._P.
>                ARR (N (V _P :$ A (NV x))) (N (V _P :$ A (NV y)))
>                ]]]]]
>     seDef = L $ "X" :. [._X.
>               L $ "x" :. [.x.
>               L $ "y" :. [.y.
>               L $ "q" :. [.q.
>               L $ "P" :. [._P.
>               L $ "px" :. [.px.
>               N (coe :@ [N (V _P :$ A (NV x)), N (V _P :$ A (NV y)),
>                   CON (N (P refl :$ A (ARR (NV _X) SET) :$ A (NV _P) :$ Out
>                             :$ A (NV x) :$ A (NV y) :$ A (NV q))),
>                   NV px])
>               ]]]]]]

>   symEq = [("Primitive", 0), ("symEq", 0)] := DEFN def :<: ty where
>     ty = PRF $ ALL SET $ L $ "X" :. [._X.
>                    ALL (NV _X) $ L $ "x" :. [.x.
>                    ALL (NV _X) $ L $ "y" :. [.y.
>                    IMP (EQBLUE (NV _X :>: NV x) (NV _X :>: NV y))
>                    (EQBLUE (NV _X :>: NV y) (NV _X :>: NV x))
>                ]]]
>     def = L $ "X" :. [._X.
>           L $ "x" :. [.x.
>           L $ "y" :. [.y.
>           L $ "q" :. [.q.
>           N (P refl :$ A (ARR (NV _X) SET)
>               :$ A (L $ "z" :. [.z.
>                   PRF (EQBLUE (NV _X :>: NV z) (NV _X :>: NV x))])
>               :$ Out
>               :$ A (NV x)
>               :$ A (NV y)
>               :$ A (NV q)
>               :$ Fst
>               :$ A (N (P refl :$ A (NV _X) :$ A (NV x))))
>           ]]]]

> import -> Primitives where
>   ("cohAx", cohAx) :
>   ("refl", refl) :
>   ("substEq", substEq) :
>   ("symEq", symEq) :


In the display syntax, a blue equality can be between arbitrary DExTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEqBlue|
to DInTm, along with appropriate elaboration and distillation rules.

> import -> DInTmConstructors where
>   DEqBlue :: DExTm p x -> DExTm p x -> DInTm p x

> import -> DInTmPretty where
>   pretty (DEqBlue t u) = wrapDoc
>       (pretty t ArgSize <+> kword KwEqBlue <+> pretty u ArgSize)
>       ArgSize

> import -> DInTmTraverse where
>   traverseDTIN f (DEqBlue t u) =
>     (| DEqBlue (traverseDTEX f t) (traverseDTEX f u) |)


> import -> KeywordConstructors where
>   KwEqBlue :: Keyword

> import -> KeywordTable where
>   key KwEqBlue = "=="

> import -> DInTmParsersMore where
>   (EqSize, \ t -> (| DEqBlue  (pFilter isEx (pure t)) (%keyword KwEqBlue%)
>                               (pFilter isEx (sizedDInTm (pred EqSize))) |)) :

> import -> ParserCode where
>   isEx :: DInTmRN -> Maybe DExTmRN
>   isEx (DN tm)  = Just tm
>   isEx _        = Nothing


> import -> MakeElabRules where
>   makeElab' loc (PROP :>: DEqBlue t u) = do
>       ttt <- subElabInfer loc t
>       utt <- subElabInfer loc u
>       let ttm :=>: tv :<: tty :=>: ttyv = extractNeutral ttt
>       let utm :=>: uv :<: uty :=>: utyv = extractNeutral utt
>       return $  EQBLUE (tty   :>: ttm)  (uty   :>: utm)
>           :=>:  EQBLUE (ttyv  :>: tv)   (utyv  :>: uv)

> import -> DistillRules where
>   distill es (PROP :>: tm@(EQBLUE (tty :>: t) (uty :>: u))) = do
>       t' <- toDExTm es (tty :>: t)
>       u' <- toDExTm es (uty :>: u)
>       return $ DEqBlue t' u' :=>: evTm tm

When distilling a proof of an equation, we first check to see if the equation
holds definitionally. If so, we avoid forcing the proof and return refl instead.

>   distill es (p@(PRF (EQBLUE (_S :>: s) (_T :>: t))) :>: q) = do
>       r <- askNSupply
>       if equal (SET :>: (_S, _T)) r && equal (_S :>: (s, t)) r
>           then return (DU :=>: N (P refl :$ A _S :$ A s))
>           else distillBase es (p :>: q)
