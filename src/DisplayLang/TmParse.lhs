\section{Parsing Terms}
\label{sec:parser}

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

> import Features.Features ()

> import Evidences.Tm

%endif

The term parser eats structured |Token|s as defined in @Lexer.lhs@. It uses the
monadic parser combinators to translate the grammar of terms defined in
Section~\ref{sec:language}.


\subsection{Names}

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


\subsection{Overall parser structure}

The |pExDTm| and |pInDTm| functions start parsing at the maximum size.

> pExDTm :: Parsley Token ExDTmRN
> pExDTm = sizedExDTm maxBound

> pInDTm :: Parsley Token InDTmRN
> pInDTm = sizedInDTm maxBound


We do not allow ascriptions in the term syntax, but they are useful in
commands, so we provide |pAscription| to parse an ascription into
separate components, and |pAscriptionTC| to parse an ascription as an
appropriate type-cast.

> pAscription :: Parsley Token (InDTmRN :<: InDTmRN)
> pAscription = (| pInDTm (%keyword KwAsc%) :<: pInDTm |)

> pAscriptionTC :: Parsley Token ExDTmRN
> pAscriptionTC = (| typecast pInDTm (%keyword KwAsc%) pInDTm |)
>   where typecast tm ty = DType ty ::$ [A tm]


Each |sized| parser tries the appropriate |special| parser for the size,
then falls back to parsing at the previous size followed by a |more| parser.
At the smallest size, brackets must be used to start parsing from the
largest size again. Concrete syntax is matched using the lists of parsers
defined in the following subsection.

> sizedExDTm :: Size -> Parsley Token ExDTmRN
> sizedExDTm z = (|(::$ []) (specialHead z) |) <|>
>       (if z > minBound  then pLoop (sizedExDTm (pred z)) (moreExDTm z)
>                         else bracket Round pExDTm)

> sizedInDTm :: Size -> Parsley Token InDTmRN
> sizedInDTm z = specialInDTm z <|> (| (DN . (::$ [])) (specialHead z) |) <|>
>       (if z > minBound  then pLoop (sizedInDTm (pred z)) (moreInEx z)
>                         else bracket Round pInDTm)

> specialHead :: Size -> Parsley Token DHEAD
> specialHead = sizeListParse headParsers

> specialInDTm :: Size -> Parsley Token InDTmRN
> specialInDTm = sizeListParse inDTmParsersSpecial

> moreInEx :: Size -> InDTmRN -> Parsley Token InDTmRN
> moreInEx z (DN e)  = (| DN (moreExDTm z e) |) <|> moreInDTm z (DN e)
> moreInEx z t       = moreInDTm z t

> moreExDTm :: Size -> ExDTmRN -> Parsley Token ExDTmRN
> moreExDTm s e = (| (e $::$) (sizeListParse elimParsers s) |)

> moreInDTm :: Size -> InDTmRN -> Parsley Token InDTmRN
> moreInDTm = paramListParse inDTmParsersMore


\subsection{Lists of sized parsers}

A |SizedParserList| is a list of parsers associated to every size; a
|ParamParserList| allows the parser to depend on a parameter.

> type SizedParserList a    = [(Size, [Parsley Token a])]
> type ParamParserList a b  = [(Size, [a -> Parsley Token b])]

We can construct such a list from a list of size-parser pairs thus:

> arrange :: [(Size, b)] -> [(Size, [b])]
> arrange xs = map (\ s -> (s,  pick s xs)) (enumFromTo minBound maxBound)
>   where
>     pick :: Eq a => a -> [(a, b)] -> [b]
>     pick x = concatMap (\ (a , b) -> if a == x then [b] else [])

To parse using a list at a particular size, we try all the parsers at that size
in order:

> sizeListParse :: SizedParserList a -> Size -> Parsley Token a
> sizeListParse sps s = pTryList . unJust $ lookup s sps

> paramListParse :: ParamParserList a b -> Size -> a -> Parsley Token b
> paramListParse sfs s a = pTryList . map ($ a) . unJust $ lookup s sfs

> unJust :: Maybe a -> a
> unJust (Just x) = x

> pTryList :: [Parsley Token a] -> Parsley Token a
> pTryList (p:ps)  = p <|> pTryList ps
> pTryList []      = (|)

Now we define the lists of parsers that actually match bits of the concrete
syntax. Note that each list has a corresponding aspect so features can extend
the parser.

> headParsers :: SizedParserList DHEAD
> headParsers = arrange $ 
>    (ArgSize, (| DType (bracket Round (keyword KwAsc *> pInDTm))|)) :
>    (ArgSize, (| DP nameParse |)) :
>    []

> elimParsers :: SizedParserList (Elim InDTmRN)
> elimParsers = arrange $ 
>     import <- ElimParsers
>   
>     (AppSize, (| Out (%keyword KwOut%) |)) :
>     (AppSize, (| A (sizedInDTm ArgSize) |)) :
>     []
      
> inDTmParsersSpecial :: SizedParserList InDTmRN
> inDTmParsersSpecial = arrange $ 
>     import <- InDTmParsersSpecial
>
>     (ArgSize, (|DSET (%keyword KwSet%)|)) :
>     (ArgSize, (|DQ (pFilter questionFilter ident)|)) :
>     (ArgSize, (|DU (%keyword KwUnderscore%)|)) :
>     (ArgSize, (|DCON (%keyword KwCon%) (sizedInDTm ArgSize)|)) :
>     (ArgSize, (|(iter mkDLAV) (%keyword KwLambda%) (some (ident <|> underscore)) (%keyword KwArr%) pInDTm|)) :
>     (AndSize, (|DPI (%keyword KwPi%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>     (PiSize, (|(flip iter)  
>                   (some (bracket Round 
>                        (|(ident <|> underscore) , (%keyword KwAsc%) pInDTm|)))
>                   (| (uncurry mkDPIV) (%keyword KwArr%)
>                    | (uncurry mkDALLV) (%keyword KwImp%) |)
>                   pInDTm |)) :
>     []

> inDTmParsersMore :: ParamParserList InDTmRN InDTmRN
> inDTmParsersMore = arrange $ 
>     import <- InDTmParsersMore

>     (ArrSize, \ s -> (| (DARR s) (%keyword KwArr%) (sizedInDTm PiSize) |)) :
>     []


\subsection{Parser support code}

> import <- ParserCode

> questionFilter :: String -> Maybe String
> questionFilter ('?':s)  = Just s
> questionFilter _        = Nothing

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


\subsection{Parsing schemes}

> pScheme :: Parsley Token (Scheme InDTmRN)
> pScheme = (|mkScheme (many pSchemeBit) (%keyword KwAsc%) pInDTm|)
>   where
>     pSchemeBit :: Parsley Token (String, Either (Scheme InDTmRN) InDTmRN)
>     pSchemeBit = bracket Round (| ident , (%keyword KwAsc%) (| (Left . SchType) pInDTm |) |)
>                  <|> bracket Curly (| ident , (%keyword KwAsc%) (| Right pInDTm |) |)
>     
>     mkScheme :: [(String, Either (Scheme InDTmRN) InDTmRN)] -> InDTmRN -> Scheme InDTmRN
>     mkScheme [] ty = SchType ty
>     mkScheme ((x, Left   s) : bits) ty = SchExplicitPi  (x :<: s) (mkScheme bits ty)
>     mkScheme ((x, Right  s) : bits) ty = SchImplicitPi  (x :<: s) (mkScheme bits ty)