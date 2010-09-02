\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Prop where

%endif


> import -> CanConstructors where
>   Prop    :: Can t
>   Prf     :: t -> Can t
>   All     :: t -> t -> Can t
>   And     :: t -> t -> Can t
>   Trivial :: Can t
>   Absurd  :: Can t
>   Box     :: Irr t -> Can t
>   Inh     :: t -> Can t
>   Wit     :: t -> Can t

Elim forms inherited from elsewhere

> import -> CanTraverse where
>   traverse _ Prop      = (|Prop|)
>   traverse f (Prf p)   = (|Prf (f p)|)
>   traverse f (All p q) = (|All (f p) (f q)|)
>   traverse f (And p q) = (|And (f p) (f q)|)
>   traverse _ Trivial   = (|Trivial|)
>   traverse _ Absurd    = (|Absurd|)
>   traverse f (Box p)   = (|Box (traverse f p)|)
>   traverse f (Inh ty)  = (|Inh (f ty)|)
>   traverse f (Wit t)   = (|Wit (f t)|)

> import -> CanHalfZip where
>   halfZip  Prop      Prop      = Just Prop
>   halfZip  (Prf p0)  (Prf p1)  = Just (Prf (p0, p1))

> import -> CanPats where
>   pattern PROP        = C Prop
>   pattern PRF p       = C (Prf p)
>   pattern ALL p q     = C (All p q)
>   pattern IMP p q     = ALL (PRF p) (L (K q))
>   pattern ALLV x s p  = ALL s (LAV x p)
>   pattern AND p q     = C (And p q)
>   pattern TRIVIAL     = C Trivial
>   pattern ABSURD      = C Absurd
>   pattern BOX p       = C (Box p)
>   pattern INH ty      = C (Inh ty)
>   pattern WIT t       = C (Wit t)

> import -> CanDisplayPats where
>   pattern DPROP        = DC Prop
>   pattern DPRF p       = DC (Prf p)
>   pattern DALL p q     = DC (All p q)
>   pattern DIMP p q     = DALL (DPRF p) (DL (DK q))
>   pattern DALLV x s p  = DALL s (DLAV x p)
>   pattern DAND p q     = DC (And p q)
>   pattern DTRIVIAL     = DC Trivial
>   pattern DABSURD      = DC Absurd
>   pattern DBOX p       = DC (Box p)
>   pattern DINH ty      = DC (Inh ty)
>   pattern DWIT t       = DC (Wit t)

> import -> CanPretty where
>   pretty Prop           = const (kword KwProp)
>   pretty (Prf p)        = wrapDoc (kword KwPrf <+> pretty p AndSize) AppSize
>   pretty (All p q)      = prettyAll empty (DALL p q)
>   pretty (And p q)      = wrapDoc
>       (pretty p (pred AndSize) <+> kword KwAnd <+> pretty q AndSize)
>       AndSize
>   pretty Trivial        = const (kword KwTrivial)
>   pretty Absurd         = const (kword KwAbsurd)
>   pretty (Box (Irr p))  = pretty p
>   pretty (Inh ty)       = wrapDoc (kword KwInh <+> pretty ty ArgSize) AppSize
>   pretty (Wit t)        = wrapDoc (kword KwWit <+> pretty t ArgSize) AppSize

> import -> Pretty where
>   prettyAll :: Doc -> DInTmRN -> Size -> Doc
>   prettyAll bs (DALL (DPRF p) (DL (DK q))) = prettyAllMore bs
>     (pretty p (pred PiSize) <+> kword KwImp <+> pretty q PiSize)
>   prettyAll bs (DALL s (DL (x ::. t))) =
>     prettyAll (bs <> parens (text x <+> kword KwAsc <+> pretty s maxBound)) t
>   prettyAll bs (DALL s (DL (DK t))) = prettyAll bs (DALL s (DL ("_" ::. t)))
>   prettyAll bs (DALL s t) = prettyAllMore bs
>     (kword KwAll <+> pretty s minBound <+> pretty t minBound)
>   prettyAll bs tm = prettyAllMore bs (pretty tm PiSize)
>
>   prettyAllMore :: Doc -> Doc -> Size -> Doc
>   prettyAllMore bs d
>     | isEmpty bs  = wrapDoc d PiSize
>     | otherwise   = wrapDoc (bs <+> kword KwImp <+> d) PiSize


> import -> CanTyRules where
>   canTy _   (Set :>: Prop) = return Prop
>   canTy chev  (Set :>: Prf p) = (|Prf (chev (PROP :>: p))|)
>   canTy chev  (Prop :>: All s p) = do
>     ssv@(_ :=>: sv) <- chev (SET :>: s)
>     ppv <- chev (ARR sv PROP :>: p)
>     return $ All ssv ppv
>   canTy chev  (Prop :>: And p q) = 
>     (|And (chev (PROP :>: p)) (chev (PROP :>: q))|)
>   canTy _  (Prop :>: Trivial) = return Trivial
>   canTy _   (Prop :>: Absurd) = return Absurd
>   canTy chev  (Prf p :>: Box (Irr x)) = (|(Box . Irr) (chev (PRF p :>: x))|)
>   canTy chev (Prf (AND p q) :>: Pair x y) = do
>     (|Pair (chev (PRF p :>: x)) (chev (PRF q :>: y))|)
>   canTy _   (Prf TRIVIAL :>: Void) = return Void
>   canTy chev (Prop :>: Inh ty) = (|Inh (chev (SET :>: ty))|)
>   canTy chev (Prf (INH ty) :>: Wit t) = (|Wit (chev (ty :>: t))|)

> import -> ElimTyRules where
>   elimTy chev (f :<: Prf (ALL p q))      (A e)  = do
>     eev@(e :=>: ev) <- chev (p :>: e)
>     return $ (A eev, PRF (q $$ A ev))
>   elimTy chev (_ :<: Prf (AND p q))      Fst    = return (Fst, PRF p)
>   elimTy chev (_ :<: Prf (AND p q))      Snd    = return (Snd, PRF q)

> import -> OpCode where
>   nEOp = Op { opName = "naughtE"
>             , opArity = 2
>             , opTyTel =  "z" :<: PRF ABSURD :-: \ _ ->
>                          "X" :<: SET :-: \ xX -> Target xX
>             , opRun = runOpTree $ OCon $ OBarf
>             , opSimp = \_ _ -> empty
>             }
>   inhEOp = Op { opName = "inh"
>               , opArity = 4
>               , opTyTel = "S" :<: SET :-: \ ty ->
>                           "p" :<: PRF (INH ty) :-: \ p ->
>                           "P" :<: IMP (PRF (INH ty)) PROP :-: \ pred ->
>                           "m" :<: PI ty (L $ "s" :. [.t.  
>                                            pred -$ [ WIT (NV t) ] ]) :-: \ _ -> 
>                           Target (PRF (pred $$ A p))
>               , opRun = \[_,p,_,m] -> case p of
>                                         WIT t -> Right $ m $$ A t
>                                         N n   -> Left n
>               , opSimp = \_ _ -> empty
>               }

> import -> Operators where
>   nEOp :
>   inhEOp :

> import -> CanEtaExpand where
>   etaExpand (Prf p :>: x) r = Just (BOX (Irr (inQuote (PRF p :>: x) r)))

> import -> Check where
>   check (PRF (ALL p q) :>: L sc)  = do
>     freshRef  ("" :<: p)
>               (\ref -> check (  PRF (q $$ A (pval ref)) :>: 
>                                 underScope sc ref))
>     return $ L sc :=>: (evTm $ L sc)

> import -> OpRunEqGreen where
>   opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
>   opRunEqGreen [PRF _,_,PRF _,_] = Right TRIVIAL

> import -> Coerce where
>   coerce Prop              q pP  = Right pP
>   coerce (Prf (pP1, pP2))  q p   = Right $ q $$ Fst $$ A p


> import -> KeywordConstructors where
>    KwProp     :: Keyword
>    KwAbsurd   :: Keyword
>    KwTrivial  :: Keyword
>    KwPrf      :: Keyword
>    KwAnd      :: Keyword
>    KwArr      :: Keyword
>    KwImp      :: Keyword
>    KwAll      :: Keyword
>    KwInh      :: Keyword
>    KwWit      :: Keyword

> import -> KeywordTable where
>   key KwProp      = "Prop"
>   key KwAbsurd    = "FF"
>   key KwTrivial   = "TT"
>   key KwPrf       = ":-"
>   key KwAnd       = "&&"
>   key KwArr       = "->"
>   key KwImp       = "=>"
>   key KwAll       = "All"
>   key KwInh       = "Inh"
>   key KwWit       = "wit"

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DPROP     (%keyword KwProp%)|)) :
>   (ArgSize, (|DABSURD   (%keyword KwAbsurd%)|)) :
>   (ArgSize, (|DTRIVIAL  (%keyword KwTrivial%)|)) :
>   (AndSize, (|DPRF      (%keyword KwPrf%) (sizedDInTm AndSize)|)) :
>   (AndSize, (|DINH      (%keyword KwInh%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DWIT      (%keyword KwWit%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DALL      (%keyword KwAll%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :

> import -> DInTmParsersMore where
>   (AndSize, \ s -> (| (DAND s) (%keyword KwAnd%) (sizedDInTm AndSize)  |)) :
>   (ArrSize, \ s -> (| (DIMP s) (%keyword KwImp%) (sizedDInTm PiSize)   |)) :



> import -> DistillRules where
>   distill es (PRF TRIVIAL :>: _) = return (DU :=>: VOID)