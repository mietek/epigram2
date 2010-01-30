\section{Parsing Terms}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module DisplayLang.TmParse where

> import Control.Applicative
> import Data.Char

> import Kit.MissingLibrary
> import Kit.Parsley

> import DisplayLang.DisplayTm
> import DisplayLang.Lexer
> import DisplayLang.Naming

> import Features.Features

> import Evidences.Tm

%endif

The Cochon's terms parser eats structured Tokens, as defined in
@Lexer.lhs@. The code uses the applicative parser to translate
the grammar of terms defined in Section~\ref{sec:language}.

A relative name is a list of idents separated by dots, and possibly
with |^| or |_| symbols (for relative or absolute offsets).

> nameParse :: Parsley Token RelName
> nameParse = do
>     s <- ident
>     case parse pName s of
>         Right rn  -> return rn
>         Left e    -> fail "nameParse failed"

> pName :: Parsley Char RelName
> pName = (| pNamePart : (many (tokenEq '.' *> pNamePart)) |)

> pNamePart :: Parsley Char (String, Offs)
> pNamePart = (|(,) pNameWord (%tokenEq '^'%) (| Rel (| read pNameOffset |) |)
>              |(,) pNameWord (%tokenEq '_'%) (| Abs (| read pNameOffset |) |)
>              |(,) pNameWord ~(Rel 0)
>              |)

> pNameWord :: Parsley Char String
> pNameWord = some (tokenFilter (\c -> not (c `elem` "_^.")))

> pNameOffset :: Parsley Char String
> pNameOffset = some (tokenFilter isDigit)



> iter :: (a -> b -> b) -> [a] -> b -> b
> iter = flip . foldr


The |pExDTm| and |pInDTm| functions start parsing at the maximum size.

> pExDTm :: Parsley Token ExDTmRN
> pExDTm = sizedExDTm maxBound

> pInDTm :: Parsley Token InDTmRN
> pInDTm = sizedInDTm maxBound


> pAscription :: Parsley Token (InDTmRN :<: InDTmRN)
> pAscription = (| (sizedInDTm (pred AscSize)) (%keyword KwAsc%) :<: pInDTm |)

> pAscriptionTC :: Parsley Token ExDTmRN
> pAscriptionTC = (| typecast (sizedInDTm (pred AscSize)) (%keyword KwAsc%) pInDTm |)
>   where typecast tm ty = (DType ty) ::$ A tm

Each |sized| parser tries the appropriate |special| parser for the size,
then falls back to parsing at the previous size followed by a |more| parser.
At the smallest size, brackets must be used to start parsing from the
largest size again.

> sizedExDTm :: Size -> Parsley Token ExDTmRN
> sizedExDTm z = specialExDTm z <|>
>       (if z > minBound  then pLoop (sizedExDTm (pred z)) (moreExDTm z)
>                         else bracket Round pExDTm)

> sizedInDTm :: Size -> Parsley Token InDTmRN
> sizedInDTm z = specialInDTm z <|> (| DN (specialExDTm z) |) <|>
>       (if z > minBound  then pLoop (sizedInDTm (pred z)) (moreInEx z)
>                         else bracket Round pInDTm)

> moreInEx :: Size -> InDTmRN -> Parsley Token InDTmRN
> moreInEx z (DN e) = DN <$> moreExDTm z e <|> moreInDTm z (DN e)
> moreInEx z t = moreInDTm z t



> specialExDTm :: Size -> Parsley Token ExDTmRN
> specialExDTm ArgSize =
>   (| DType (bracket Round (keyword KwAsc *> pInDTm))
>    | DP nameParse
>    |)

> specialExDTm z = (|)

> moreExDTm :: Size -> ExDTmRN -> Parsley Token ExDTmRN
> moreExDTm AppSize e = (e ::$) <$>
>   (| Fst (%keyword KwFst%)
>    | Snd (%keyword KwSnd%)
>    | Out (%keyword KwOut%)
>    | Call (%keyword KwCall%) ~Dum
>    | A (sizedInDTm ArgSize)
>    |)
> moreExDTm z _ = (|)

> specialInDTm :: Size -> Parsley Token InDTmRN
> specialInDTm ArgSize =
>     (|DSET (%keyword KwSet%) 
>      |DPROP (%keyword KwProp%)
>      |DUID (%keyword KwUId%)
>      |DABSURD (%keyword KwAbsurd%)
>      |DTRIVIAL (%keyword KwTrivial%)
>      |DQ (pFilter question ident)
>      |DU (%keyword KwUnderscore%)
>      |DCON (%keyword KwCon%) (sizedInDTm ArgSize)
>      |DRETURN (%keyword KwReturn%) (sizedInDTm ArgSize)
>      |DTAG (%keyword KwTag%) ident
>      |DLABEL (%keyword KwLabel%) (sizedInDTm AppSize) (%keyword KwAsc%) (sizedInDTm ArgSize) (%keyword KwLabelEnd%)
>      |DLRET (%keyword KwRet%) (sizedInDTm ArgSize)
>      |(iter mkDLAV) (%keyword KwLambda%) (some (ident <|> underscore)) (%keyword KwArr%) pInDTm
>      |id (bracket Square tuple)
>      |mkNum (|read digits|) (optional $ (keyword KwPlus) *> sizedInDTm ArgSize)
>      |id (%keyword KwSig%) (bracket Round sigma)
>      |DSIGMA (%keyword KwSig%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |)
>   where
>     question :: String -> Maybe String
>     question ('?':s)  = Just s
>     question _        = Nothing
>
>     tuple :: Parsley Token InDTmRN
>     tuple =
>         (|DPAIR (sizedInDTm ArgSize) (| id (%keyword KwComma%) pInDTm
>                                       | id tuple |)
>          |DVOID (% pEndOfStream %)
>          |)

>     sigma :: Parsley Token InDTmRN
>     sigma = (|mkSigma (optional (ident <* keyword KwAsc)) pInDTm sigmaMore
>              |DUNIT (% pEndOfStream %)
>              |)

>     sigmaMore :: Parsley Token InDTmRN
>     sigmaMore = (|id (% keyword KwSemi %) (sigma <|> pInDTm)
>                  |(\p s -> mkSigma Nothing (DPRF p) s) (% keyword KwPrf %) pInDTm sigmaMore
>                  |(\x -> DPRF x) (% keyword KwPrf %) pInDTm
>                  |)

>     mkSigma :: Maybe String -> InDTmRN -> InDTmRN -> InDTmRN
>     mkSigma Nothing s t = DSIGMA s (DL (DK t))
>     mkSigma (Just x) s t = DSIGMA s (DL (x ::. t))

>     mkNum :: Int -> Maybe InDTmRN -> InDTmRN
>     mkNum 0 Nothing = DZE
>     mkNum 0 (Just t) = t
>     mkNum n t = DSU (mkNum (n-1) t)

> specialInDTm AndSize =
>     (|DPRF (%keyword KwPrf%) (sizedInDTm AndSize)
>      |(DMU Nothing) (%keyword KwMu%) (sizedInDTm ArgSize)
>      |(DIMU Nothing) (%keyword KwIMu%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DIDESC (%keyword KwIDesc%) (sizedInDTm ArgSize)
>      |DIDONE (%keyword KwIDone%) (sizedInDTm ArgSize)
>      |DIARG (%keyword KwIArg%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DIIND1 (%keyword KwIInd1%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DIIND (%keyword KwIInd%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DNU (%keyword KwNu%) (sizedInDTm ArgSize)
>      |DINU (%keyword KwINu%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DINH (%keyword KwInh%) (sizedInDTm ArgSize)
>      |DWIT (%keyword KwWit%) (sizedInDTm ArgSize)
>      |(DCOIT DVOID) (%keyword KwCoIt%)
>         (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |(DICOIT DVOID) (%keyword KwICoIt%)
>         (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>         (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DMONAD (%keyword KwMonad%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DQUOTIENT (%keyword KwQuotient%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DENUMT (%keyword KwEnum%) (sizedInDTm ArgSize)
>      |DPI (%keyword KwPi%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DALL (%keyword KwAll%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |)

> specialInDTm PiSize =
>     (|(flip iter)  (some (bracket Round (|(ident <|> underscore) , (%keyword KwAsc%) pInDTm|)))
>                    (| (uncurry mkDPIV) (%keyword KwArr%) | (uncurry mkDALLV) (%keyword KwImp%) |)
>                    pInDTm |)

> specialInDTm z = (|)

> moreInDTm :: Size -> InDTmRN -> Parsley Token InDTmRN
> moreInDTm EqSize t =
>   (| DEqBlue  (pFilter isEx (pure t)) (%keyword KwEqBlue%)
>              (pFilter isEx (sizedInDTm (pred EqSize)))
>    |) <|> moreInDTm (pred EqSize) t
> moreInDTm AndSize s =
>   (| (DAND s) (%keyword KwAnd%) (sizedInDTm AndSize)
>    |)
> moreInDTm ArrSize s =
>   (| (DARR s) (%keyword KwArr%) (sizedInDTm PiSize)
>    | (DIMP s) (%keyword KwImp%) (sizedInDTm PiSize)
>    |)
> moreInDTm z _ = (|)


> isEx :: InDTmRN -> Maybe ExDTmRN
> isEx (DN tm)  = Just tm
> isEx _        = Nothing



> underscore :: Parsley Token String
> underscore = keyword KwUnderscore >> pure "_"

> mkDLAV :: String -> InDTmRN -> InDTmRN
> mkDLAV "_"  t = DL (DK t)
> mkDLAV x    t = DLAV x t

> mkDPIV :: String -> InDTmRN -> InDTmRN -> InDTmRN
> mkDPIV   "_"  s t = DPI s (DL (DK t))
> mkDPIV   x    s t = DPIV x s t

> mkDALLV :: String -> InDTmRN -> InDTmRN -> InDTmRN
> mkDALLV  "_"  s p = DALL s (DL (DK p))
> mkDALLV  x    s p = DALLV x s p