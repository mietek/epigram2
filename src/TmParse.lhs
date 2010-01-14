\section{Parsing Terms}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module TmParse where

> import MissingLibrary
> import Control.Applicative
> import Data.Foldable hiding (foldr)
> import Data.Traversable
> import Data.Char

> import BwdFwd
> import Developments
> import DisplayTm
> import Features
> import Lexer
> import Naming
> import Parsley
> import Tm
> import Rules

%endif

The Cochon's terms parser eats structured Tokens, as defined in
@Lexer.lhs@. The code uses the applicative parser to translate
the grammar of terms defined in Section~\ref{sec:language}.

A relative name is a list of idents separated by dots, and possibly
with |^| or |_| symbols (for relative or absolute offsets).

> nameParse :: Parsley Token RelName
> nameParse = (|namePartParse : (many $ keyword "." *> namePartParse)|)

> namePartParse :: Parsley Token (String, Offs)
> namePartParse =  (|(,) ident (%keyword "^"%) (| Rel (| read digits |) |)
>                   |(,) ident (%keyword "_"%) (| Abs (| read digits |) |)
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
> pAscription = (| sizedInDTm (pred AscSize) (%keyword ":"%) ::? pInDTm |)

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
>   (|DN (| (t ::?) (%keyword ":"%) pInDTm |)|) <|> moreInEx (pred AscSize) t
> moreInEx z (DN e) = DN <$> moreExDTm z e <|> moreInDTm z (DN e)
> moreInEx z t = moreInDTm z t



> specialExDTm :: Size -> Parsley Token ExDTmRN
> specialExDTm ArgSize =
>   (| pFilter findOp ident ::@ bracket Round (pSep (keyword ",") pInDTm)
>    | DP nameParse
>    |)
>   where
>     findOp name = find (\op -> opName op == name) operators

This case causes a massive drop in performance, so it is temporarily
switched off. To forcibly parse a type ascription, use |pAscription|.
We need to sort out a better solution for ascription syntax.

> -- specialExDTm AscSize =
> --  (| sizedInDTm (pred AscSize) (%keyword ":"%) ::? pInDTm |)

> specialExDTm z = (|)

> moreExDTm :: Size -> ExDTmRN -> Parsley Token ExDTmRN
> moreExDTm AscSize e =
>   (| (DN e ::?) (%keyword ":"%) pInDTm |) <|> moreExDTm (pred AscSize) e
> moreExDTm AppSize e = (e ::$) <$>
>   (| Fst (%keyword "!"%)
>    | Snd (%keyword "-"%)
>    | Out (%keyword "%"%)
>    | Call (%keyword "call"%) ~Dum
>    | A (sizedInDTm ArgSize)
>    |)
> moreExDTm EqSize e =
>   (|eqG  (pFilter isEqSide (pure (DN e))) (%keyword "<->"%)
>          (pFilter isEqSide (sizedInDTm (pred EqSize)))
>    |) <|> moreExDTm (pred EqSize) e
>   where
>     eqG (y0 :>: t0) (y1 :>: t1) = eqGreen ::@ [y0, t0, y1, t1]
> moreExDTm z _ = (|)

> specialInDTm :: Size -> Parsley Token InDTmRN
> specialInDTm ArgSize =
>     (|DSET (%keyword "*"%) 
>      |DPROP (%keyword "#"%)
>      |DABSURD (%keyword "FF"%)
>      |DTRIVIAL (%keyword "TT"%)
>      |DQ (%keyword "?"%) (ident <|> pure "")
>      |DCON (%keyword "@"%) (sizedInDTm ArgSize)
>      |DRETURN (%keyword "'"%) (sizedInDTm ArgSize)
>      |DTAG (%keyword "`"%) ident
>      |DLABEL (%keyword "<"%) (sizedInDTm AppSize) (%keyword ":"%) (sizedInDTm ArgSize) (%keyword ">"%)
>      |DLRET (%keyword "return"%) (sizedInDTm ArgSize)
>      |(iter DLAV) (%keyword "\\"%) (some ident) (%keyword "->"%) pInDTm
>      |id (bracket Square tuple)
>      |DENUMT (bracket Curly (|  (iter (DCONSE . DTAG)) (pSep (keyword ",") ident)
>                                (| id (%keyword "/"%) pInDTm | DNILE |)|))
>      |mkNum (|read digits|) (optional $ (keyword "+") *> sizedInDTm ArgSize)
>      |id (bracket Round sigma)
>      |)
>   where
>     tuple :: Parsley Token InDTmRN
>     tuple =
>         (|DPAIR (sizedInDTm ArgSize) (| id (%keyword "/"%) pInDTm | id tuple |)
>          |DVOID (% pEndOfStream %)
>          |)

>     sigma :: Parsley Token InDTmRN
>     sigma = (|mkSigma (optional (ident <* keyword ":")) pInDTm sigmaMore
>              |DUNIT (% pEndOfStream %)
>              |)

>     sigmaMore :: Parsley Token InDTmRN
>     sigmaMore = (|id (% keyword ";" %) (sigma <|> pInDTm)
>                  |(\p s -> mkSigma Nothing (DPRF p) s) (% keyword ":-" %) pInDTm sigmaMore
>                  |(\x -> DPRF x) (% keyword ":-" %) pInDTm
>                  |)

>     mkSigma :: Maybe String -> InDTmRN -> InDTmRN -> InDTmRN
>     mkSigma Nothing s t = DSIGMA s (DL (DK t))
>     mkSigma (Just x) s t = DSIGMA s (DL (x ::. t))

>     mkNum :: Int -> Maybe InDTmRN -> InDTmRN
>     mkNum 0 Nothing = DZE
>     mkNum 0 (Just t) = t
>     mkNum n t = DSU (mkNum (n-1) t)

> specialInDTm AndSize =
>     (|DPRF (%keyword ":-"%) (sizedInDTm AndSize)
>      |(DMU Nothing) (%keyword "Mu"%) (sizedInDTm ArgSize)
>      |(DIMU Nothing) (%keyword "IMu"%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DIDESC (%keyword "IDesc"%) (sizedInDTm ArgSize)
>      |DIDONE (%keyword "IDone"%) (sizedInDTm ArgSize)
>      |DIARG (%keyword "IArg"%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DIIND1 (%keyword "IInd1"%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DIIND (%keyword "IND"%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DNU (%keyword "Nu"%) (sizedInDTm ArgSize)
>      |DINH (%keyword "Inh"%) (sizedInDTm ArgSize)
>      |DWIT (%keyword "wit"%) (sizedInDTm ArgSize)
>      |(DCOIT DVOID) (%keyword "CoIt"%)
>         (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DMONAD (%keyword "Monad"%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |DQUOTIENT (%keyword "Quotient"%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>      |)

> specialInDTm PiSize =
>     (|(flip iter)  (some (bracket Round (|ident, (%keyword ":"%) pInDTm|)))
>                    (| (uncurry DPIV) (%keyword "->"%) | (uncurry DALLV) (%keyword "=>"%) |)
>                    pInDTm |)

> specialInDTm z = (|)

> moreInDTm :: Size -> InDTmRN -> Parsley Token InDTmRN
> moreInDTm EqSize t =
>   (| DEqBlue  (pFilter isEx (pure t)) (%keyword "=="%)
>              (pFilter isEx (sizedInDTm (pred EqSize)))
>    |) <|> moreInDTm (pred EqSize) t
> moreInDTm AndSize s =
>   (| (DAND s) (%keyword "&&"%) (sizedInDTm AndSize)
>    |)
> moreInDTm ArrSize s =
>   (| (DARR s) (%keyword "->"%) (sizedInDTm ArrSize)
>    | (DIMP s) (%keyword "=>"%) (sizedInDTm ArrSize)
>    |)
> moreInDTm z _ = (|)

> isEqSide :: InDTmRN -> Maybe (InDTmRN :>: InDTmRN)
> isEqSide (DN (t0 ::? y0)) = Just (y0 :>: t0)
> isEqSide _ = Nothing

> isEx :: InDTmRN -> Maybe ExDTmRN
> isEx (DN tm)  = Just tm
> isEx _        = Nothing