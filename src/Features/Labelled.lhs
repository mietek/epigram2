\section{Labelled Types}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Labelled where

%endif

> import -> CanConstructors where
>   Label  :: t -> t -> Can t
>   LRet   :: t -> Can t

> import -> ElimConstructors where
>   Call   :: t -> Elim t

> import -> CanPats where
>   pattern LABEL l t = C (Label l t)
>   pattern LRET t    = C (LRet t)

> import -> CanDisplayPats where
>   pattern DLABEL l t = DC (Label l t)
>   pattern DLRET t    = DC (LRet t)

> import -> CanCompile where
>   makeBody (Label l t) = makeBody t
>   makeBody (LRet t)    = makeBody t

> import -> CanTraverse where
>   traverse f (Label l t) = (| Label (f l) (f t) |)
>   traverse f (LRet t)    = (| LRet (f t) |)

> import -> ElimTraverse where
>   traverse f (Call l) = (| Call (f l) |)

> import -> CanHalfZip where
>   halfZip (Label l1 t1) (Label l2 t2) = Just (Label (l1,l2) (t1,t2))
>   halfZip (LRet x) (LRet y)           = Just (LRet (x,y))

> import -> ElimHalfZip where
>   halfZip (Call t1) (Call t2) = Just (Call (t1, t2))

> import -> CanPretty where
>   pretty (Label l t) = const (kword KwLabel <+>
>       pretty l maxBound <+> kword KwAsc <+> pretty t maxBound
>       <+> kword KwLabelEnd)
>   pretty (LRet x) = wrapDoc (kword KwRet <+> pretty x ArgSize) ArgSize

> import -> ElimPretty where
>   pretty (Call _) = const (kword KwCall)

> import -> ElimComputation where
>   LRET t $$ Call l = t

> import -> ElimCompile where
>   makeBody (arg, Call l) = makeBody arg

> import -> CanTyRules where
>   canTy chev (Set :>: Label l t) = do
>      ttv@(t :=>: tv) <- chev (SET :>: t)
>      llv@(l :=>: lv) <- chev (tv :>: l)
>      return (Label llv ttv)
>   canTy chev (Label l ty :>: LRet t) = do
>      ttv@(t :=>: tv) <- chev (ty :>: t)
>      return (LRet ttv)

> import -> ElimTyRules where
>   elimTy chev (_ :<: Label _ t) (Call l) = do
>      llv@(l :=>: lv) <- chev (t :>: l)
>      return (Call llv, t)

> import -> Coerce where
>   coerce (Label (l1, l2) (t1, t2)) q (LRET t) =
>       Right $ LRET $ coe @@ [t1, t2, CON (q $$ Snd), t]


> import -> KeywordConstructors where
>   KwCall      :: Keyword
>   KwLabel     :: Keyword
>   KwLabelEnd  :: Keyword
>   KwRet       :: Keyword

> import -> KeywordTable where
>   key KwCall      = "call"
>   key KwLabel     = "<"
>   key KwLabelEnd  = ">"
>   key KwRet       = "return"  -- rename me

> import -> ElimParsers where
>   (AppSize, (| Call (%keyword KwCall%) ~DU |)) :

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DLABEL (%keyword KwLabel%) (sizedDInTm AppSize) (%keyword KwAsc%) (sizedDInTm ArgSize) (%keyword KwLabelEnd%)|)) :
>   (ArgSize, (|DLRET (%keyword KwRet%) (sizedDInTm ArgSize)|)) :


If we spot a neutral term being called when distilling, we distill the label
instead, thereby replacing horrible stuck inductions with the pretty functions
they implement.

> import -> DistillInferRules where
>   distillInfer es (t :$ Call (N l)) as = distillInfer es l as


\question{The following is all commented out. Is it detritus?}

<   canTy chev (ty :>: Call c tm) = do
<      tytv@(ty :=>: tyv) <- chev (SET :>: ty)
<      ccv@(c :=>: cv) <- chev (ty :>: c)
<      tmtv@(tm :=>: tmv) <- chev (LABEL cv ty :>: tm)
<      return (Call ccv tmtv)

< import -> OpCode where
<   callOp = Op
<     { opName = "call"
<     , opArity = 3
<     , opTy = callOpTy
<     , opRun = callOpRun       
<     , opSimp = callOpSimp
<     } where
<       callOpTy chev [ty, lbl, tm] = do
<            tytv@(ty :=>: tyv) <- chev (SET :>: ty)
<            lbltv@(lbl :=>: lblv) <- chev (tytv :>: lbl)
<            tmtv@(tm :=>: tmv) <- chev (LABEL lbltv tytv :>: tm)
<            return ([tytv, lbltv, tmtv], tyv)

<       callOpRun :: [VAL] -> Either NEU VAL
<       callOpRun [ty, lbl, LRET t] = Right t
<       callOpRun [ty, lbl, N t] = Left t

<       callOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
<       callOpSimp _ _ = empty

< import -> Operators where
<   callOp :

< import -> OpCompile where
<   ("call", [ty, l, t]) -> l

