\section{Parsing Terms}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module DisplayLang.TmParse where

> import Control.Applicative
> import Data.Foldable hiding (foldr)

> import Kit.MissingLibrary
> import Kit.Parsley

> import DisplayLang.DisplayTm
> import DisplayLang.Lexer
> import DisplayLang.Naming

> import Features.Features

> import Evidences.Tm
> import Evidences.Rules

%endif

The Cochon's terms parser eats structured Tokens, as defined in
@Lexer.lhs@. The code uses the applicative parser to translate
the grammar of terms defined in Section~\ref{sec:language}.

A relative name is a list of idents separated by dots, and possibly
with |^| or |_| symbols (for relative or absolute offsets).

> nameParse :: Parsley Token RelName
> nameParse = (|namePartParse : (many $ keyword KwNameSep *> namePartParse)|)

> namePartParse :: Parsley Token (String, Offs)
> namePartParse =  (|(,) ident (%keyword KwRelSep%) (| Rel (| read digits |) |)
>                   |(,) ident (%keyword KwAbsSep%) (| Abs (| read digits |) |)
>                   |(,) ident ~(Rel 0)
>                   |)


> iter :: (a -> b -> b) -> [a] -> b -> b
> iter = flip . foldr


The |pExDTm| and |pInDTm| functions start parsing at the maximum size.

> pExDTm :: Parsley Token ExDTmRN
> pExDTm = sizedExDTm maxBound

> pInDTm :: Parsley Token InDTmRN
> pInDTm = sizedInDTm maxBound


> pAscription :: Parsley Token ExDTmRN
> pAscription = (| sizedInDTm (pred AscSize) (%keyword KwAsc%) ::? pInDTm |)

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
> moreInEx AscSize t =
>   (|DN (| (t ::?) (%keyword KwAsc%) pInDTm |)|) <|> moreInEx (pred AscSize) t
> moreInEx z (DN e) = DN <$> moreExDTm z e <|> moreInDTm z (DN e)
> moreInEx z t = moreInDTm z t



> specialExDTm :: Size -> Parsley Token ExDTmRN
> specialExDTm ArgSize =
>   (| pFilter findOp ident ::@ bracket Round (pSep (keyword KwComma) pInDTm)
>    | DP nameParse
>    |)
>   where
>     findOp name = find (\op -> opName op == name) operators

This case causes a massive drop in performance, so it is temporarily
switched off. To forcibly parse a type ascription, use |pAscription|.
We need to sort out a better solution for ascription syntax.

> -- specialExDTm AscSize =
> --  (| sizedInDTm (pred AscSize) (%keyword KwAsc%) ::? pInDTm |)

> specialExDTm z = (|)

> moreExDTm :: Size -> ExDTmRN -> Parsley Token ExDTmRN
> moreExDTm AscSize e =
>   (| (DN e ::?) (%keyword KwAsc%) pInDTm |) <|> moreExDTm (pred AscSize) e
> moreExDTm AppSize e = (e ::$) <$>
>   (| Fst (%keyword KwFst%)
>    | Snd (%keyword KwSnd%)
>    | Out (%keyword KwOut%)
>    | Call (%keyword KwCall%) ~Dum
>    | A (sizedInDTm ArgSize)
>    |)
> moreExDTm EqSize e =
>   (|eqG  (pFilter isEqSide (pure (DN e))) (%keyword KwEqGreen%)
>          (pFilter isEqSide (sizedInDTm (pred EqSize)))
>    |) <|> moreExDTm (pred EqSize) e
>   where
>     eqG (y0 :>: t0) (y1 :>: t1) = eqGreen ::@ [y0, t0, y1, t1]
> moreExDTm z _ = (|)

> specialInDTm :: Size -> Parsley Token InDTmRN
> specialInDTm ArgSize =
>     (|DSET (%keyword KwSet%) 
>      |DPROP (%keyword KwProp%)
>      |DUID (%keyword KwUId%)
>      |DABSURD (%keyword KwAbsurd%)
>      |DTRIVIAL (%keyword KwTrivial%)
>      |DQ (%keyword KwQ%) (ident <|> pure "")
>      |DCON (%keyword KwCon%) (sizedInDTm ArgSize)
>      |DRETURN (%keyword KwReturn%) (sizedInDTm ArgSize)
>      |DTAG (%keyword KwTag%) ident
>      |DLABEL (%keyword KwLabel%) (sizedInDTm AppSize) (%keyword KwAsc%) (sizedInDTm ArgSize) (%keyword KwLabelEnd%)
>      |DLRET (%keyword KwRet%) (sizedInDTm ArgSize)
>      |(iter DLAV) (%keyword KwLambda%) (some ident) (%keyword KwArr%) pInDTm
>      |id (bracket Square tuple)
>      |mkNum (|read digits|) (optional $ (keyword KwPlus) *> sizedInDTm ArgSize)
>      |id (%keyword KwSig%) (bracket Round sigma)
>      |DSIGMA (%keyword KwSig%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |)
>   where
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
>      |)

> specialInDTm PiSize =
>     (|(flip iter)  (some (bracket Round (|ident, (%keyword KwAsc%) pInDTm|)))
>                    (| (uncurry DPIV) (%keyword KwArr%) | (uncurry DALLV) (%keyword KwImp%) |)
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
>   (| (DARR s) (%keyword KwArr%) (sizedInDTm ArrSize)
>    | (DIMP s) (%keyword KwImp%) (sizedInDTm ArrSize)
>    |)
> moreInDTm z _ = (|)

> isEqSide :: InDTmRN -> Maybe (InDTmRN :>: InDTmRN)
> isEqSide (DN (t0 ::? y0)) = Just (y0 :>: t0)
> isEqSide _ = Nothing

> isEx :: InDTmRN -> Maybe ExDTmRN
> isEx (DN tm)  = Just tm
> isEx _        = Nothing