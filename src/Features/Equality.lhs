\section{Equality}
\label{sec:features_equality}

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


We do not pretty-print |EqBlue| because it is replaced in the display syntax
by |DEqBlue| defined below.

< import -> CanPretty where


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
>            oprun [_, _, N (P r :$ A _ :$ A _) , v] | r == refl = Right v
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

> import -> Operators where
>   eqGreen :
>   coe :

> import -> AxCode where
>   coh = [("Axiom",0),("coh",0)] := (DECL :<: cohType) where
>     cohType = PRF $ 
>               ALL SET (L . HF "x" $ \x ->
>               ALL SET (L . HF "y" $ \y ->
>               ALL (PRF (EQBLUE (SET :>: x) (SET :>: y))) (L . HF "q" $ \q ->
>               ALL x (L . HF "s" $ \s ->
>               EQBLUE (x :>: s) (y :>: (coe @@ [x, y, q, s]))))))
>   refl = [("Axiom",0),("refl",0)] := (DECL :<: reflType) where
>     reflType = PRF (ALL SET (L . HF "s" $ \s ->
>                     ALL s   (L . HF "x" $ \x ->
>                     EQBLUE (s :>: x) (s :>: x))))

> import -> Axioms where
>   ("coh", coh) :
>   ("refl", refl) :


In the display syntax, a blue equality can be between arbitrary ExDTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEqBlue|
to InDTm, along with appropriate elaboration and distillation rules.

> import -> InDTmConstructors where
>   DEqBlue :: ExDTm p x -> ExDTm p x -> InDTm p x

> import -> InDTmPretty where
>   pretty (DEqBlue t u) = wrapDoc
>       (pretty t ArgSize <+> kword KwEqBlue <+> pretty u ArgSize)
>       ArgSize

> import -> InDTmTraverse where
>   traverseDTIN f (DEqBlue t u) =
>     (| DEqBlue (traverseDTEX f t) (traverseDTEX f u) |)


> import -> KeywordConstructors where
>   KwEqBlue :: Keyword

> import -> KeywordTable where
>   key KwEqBlue = "=="

> import -> InDTmParsersMore where
>   (EqSize, \ t -> (| DEqBlue  (pFilter isEx (pure t)) (%keyword KwEqBlue%)
>                               (pFilter isEx (sizedInDTm (pred EqSize))) |)) :

> import -> ParserCode where
>   isEx :: InDTmRN -> Maybe ExDTmRN
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
>       t' <- toExDTm es (tty :>: t)
>       u' <- toExDTm es (uty :>: u)
>       return $ DEqBlue t' u' :=>: evTm tm