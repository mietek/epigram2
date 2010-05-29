\section{UId}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.UId where

%endif


> import -> CanConstructors where
>   UId    :: Can t
>   Tag    :: String -> Can t

> import -> CanPats where
>   pattern UID    = C UId
>   pattern TAG s  = C (Tag s)

> import -> CanDisplayPats where
>   pattern DUID    = DC UId
>   pattern DTAG s  = DTag s []

> import -> CanTraverse where
>   traverse f UId          = (|UId|)
>   traverse f (Tag s)      = (|(Tag s)|)

> import -> CanPretty where
>   pretty UId      = const (kword KwUId)
>   pretty (Tag s)  = const (kword KwTag <> text s)

> import -> CanTyRules where
>   canTy _  (Set :>: UId)    = return UId
>   canTy _  (UId :>: Tag s)  = return (Tag s)

> import -> CanHalfZip where
>   halfZip UId UId = Just UId
>   halfZip (Tag s) (Tag s') | s == s' = Just (Tag s)

> import -> OpRunEqGreen where
>   opRunEqGreen [UID,TAG s1,UID,TAG s2] | s1 == s2 = Right $ TRIVIAL
>   opRunEqGreen [UID,TAG _,UID,TAG _] = Right $ ABSURD

> import -> Coerce where
>   coerce UId _ u = Right u


> import -> KeywordConstructors where
>   KwUId  :: Keyword
>   KwTag  :: Keyword

> import -> KeywordTable where
>   key KwUId       = "UId"
>   key KwTag       = "'"

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DUID (%keyword KwUId%)|)) :
>   (ArgSize, (|DTAG (%keyword KwTag%) ident|)) :
>   (AppSize, (|DTag (%keyword KwTag%) ident (many (sizedDInTm ArgSize))|)) :

> import -> DInTmConstructors where
>   DTag :: String -> [DInTm p x] -> DInTm p x

> import -> DInTmPretty where
>   pretty (DTAG s)     = const (kword KwTag <> text s)
>   pretty (DTag s xs)  = wrapDoc (kword KwTag <> text s
>       <+> hsep (map (flip pretty ArgSize) xs)) AppSize

> import -> DInTmTraverse where
>   traverseDTIN f (DTag s xs) = (|(DTag s) (traverse (traverseDTIN f) xs)|)

> import -> MakeElabRules where
>   makeElab' loc (UID :>: DTAG s) = return $ TAG s :=>: TAG s