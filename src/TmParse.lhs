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
> import Lexer
> import Naming
> import Parsley
> import Tm
> import Rules

%endif

The Cochon's terms parser eats structured Tokens, as defined in
@Lexer.lhs@. Using |parseTerm|, you will be able to build a nice
|INTM| in a correct context.

There is nothing fancy here. The code is simply using the applicative
parser to translate the grammar of terms. The grammar was informally
defined in Section~\ref{sec:language}.

\subsection{Matching |InTm|}

To deal with the left-recursive madness, we parse |InTm| (as well as
|ExTm|), using two mutually recursive functions: |bigInTm| and
|littleInTm|. The basic scheme is the following:

< bigInTm ::= ...
<           | ...
<           | ...
<           | littleInTm
< littleInTm ::= ...
<              | ...
<              | ...
<              | ( bigInTm )

Where |littleInTm| contains only the non-ambiguous ``base'' cases:
each of these cases allows us to unambiguously consume tokens. On the
other hand, |bigInTm| typically contains operations which might go
left, and will do so with |littleInTm|.


> bigInTm :: Parsley Token InTmRN
> bigInTm = 
>     (|id piForallParse
>      |id sigmaParse
>      |id blueEqParse
>      |PRF (%keyword ":-"%) bigInTm
>      |(MU Nothing)  (%keyword "Mu"%) bigInTm
>      |id (pLoop littleInTm pLAfter)
>      |N bigExTm
>      |)

> littleInTm :: Parsley Token InTmRN
> littleInTm =
>     (|C ~ Set (%keyword "*"%) 
>      |C ~ Prop (%keyword "#"%)
>      |C ~ Absurd (%keyword "FF"%)
>      |C ~ Trivial (%keyword "TT"%)
>      |Q (%keyword "?"%) maybeIdent
>      |CON (%keyword "@"%) littleInTm
>      |TAG (%keyword "`"%) ident
>      |id lamParse
>      |id tupleParse
>      |id enumParse
>      |id natParse
>      |N littleExTm
>      |id (bracket Round bigInTm)
>      |)
>   where
>     maybeIdent :: Parsley Token String
>     maybeIdent = ident <|> pure ""

> pLAfter :: InTmRN -> Parsley Token InTmRN
> pLAfter s =
>      (| (ARR s) (%keyword "->"%) bigInTm
>       | (IMP s) (%keyword "=>"%) bigInTm
>       | (AND s) (%keyword "&&"%) bigInTm
>       |)

> telescope :: Parsley Token [(String, InTmRN)]
> telescope = some (bracket Round (|ident, (%keyword ":"%) bigInTm|))

> piForallParse :: Parsley Token InTmRN
> piForallParse = (|mkPiForall telescope (|(,) ~mkPi (%keyword "->"%) bigInTm
>                                         |(,) ~mkForall (%keyword "=>"%) bigInTm|)|)
>     where mkPi (x,s) t = PI s (L (x :. t))
>           mkForall (x,s) t = ALL s (L (x :. t))
>           mkPiForall xs (f,t) = foldr f t xs

> arrParse :: Parsley Token InTmRN
> arrParse = (|ARR littleInTm (%keyword "->"%) bigInTm
>             |IMP littleInTm (%keyword "=>"%) bigInTm|)

> lamParse :: Parsley Token InTmRN
> lamParse = (|(flip $ foldr mkLam) (%keyword "\\"%) (some ident) (%keyword "->"%) bigInTm|)
>     where mkLam x t = L (x :. t)

> sigmaParse :: Parsley Token InTmRN
> sigmaParse = bracket Round sigma
>     where sigma = (|mkSigma (optional (ident <* keyword ":")) bigInTm sigmaMore
>                    |C ~ Unit (% pEndOfStream %)
>                    |)
>           sigmaMore = (|id (% keyword ";" %) (sigma <|> bigInTm)
>                        |(\p s -> mkSigma Nothing (PRF p) s) (% keyword ":-" %) bigInTm sigmaMore
>                        |(\x -> PRF x) (% keyword ":-" %) bigInTm
>                        |)
>           mkSigma Nothing s t = C $ Sigma s (L (K t))
>           mkSigma (Just x) s t = C (Sigma s (L (x :. t)))
>           

> andParse :: Parsley Token InTmRN
> andParse = (|(\p q -> AND p q) littleInTm 
>                                (%keyword "&&"%) 
>                                littleInTm|)

> tupleParse :: Parsley Token InTmRN
> tupleParse = bracket Square tuple 
>     where tuple = (|(\p q -> PAIR p q) littleInTm (|id tuple
>                                                    |id (%keyword "/"%) bigInTm |)
>                    |C ~ Void (% pEndOfStream %) |)

> enumParse :: Parsley Token InTmRN
> enumParse = bracket Curly (|(\t -> ENUMT t) enum|)
>     where enum = (|mkEnum (pSep (keyword ",") ident) 
>                           (optional $ (keyword "/" *> bigInTm))|)
>           mkEnum names Nothing = mkEnum' names NILE
>           mkEnum names (Just t) = mkEnum' names t
>           mkEnum' = flip $ foldr (\t e -> CONSE (TAG t) e) 

> blueEqParse :: Parsley Token InTmRN
> blueEqParse = (|mkBlueEq parseTerm (%keyword "=="%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleInTm (%keyword ":"%) littleInTm|)
>           mkBlueEq (x1,t1) (x2,t2) = EQBLUE (t1 :>: x1) (t2 :>: x2)

> natParse :: Parsley Token InTmRN
> natParse = (|mkNum digits (optional $ (keyword "+") *> littleInTm)|)
>     where mkNum num Nothing = mkNum' (read num) ZE
>           mkNum num (Just t) = mkNum' (read num) t
>           mkNum' 0 t = t
>           mkNum' n t = mkNum' (n-1) (SU t)

\subsection{Matching |ExTm|}

> bigExTm :: Parsley Token ExTmRN
> bigExTm = 
>     (|id appParse
>      |id ascriptionParse
>      |id littleExTm
>      |)


> littleExTm :: Parsley Token ExTmRN
> littleExTm = 
>     (|id operatorParse
>      |id greenEqParse 
>      |id variableParse
>      |id (bracket Round bigExTm)
>      |)

> appParse :: Parsley Token ExTmRN
> appParse =
>     pLoop littleExTm $ \f -> 
>     (|(f :$) (| (%keyword "!"%) Fst
>               | (%keyword "-"%) Snd
>               | (%keyword "%"%) Out
>               | A littleInTm|)|)

> ascriptionParse :: Parsley Token ExTmRN
> ascriptionParse = (| (:?) littleInTm (%keyword ":"%) bigInTm |)

> operatorParse :: Parsley Token ExTmRN
> operatorParse = (|mkOp (pFilter findOp ident) (bracket Round (pSep (keyword ",") bigInTm))|)
>     where mkOp op args = op :@ args
>           findOp name = find (\op -> opName op == name) operators 

> greenEqParse :: Parsley Token ExTmRN
> greenEqParse = (|mkGreenEq parseTerm (%keyword "<->"%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleInTm (%keyword ":"%) littleInTm|)
>           mkGreenEq (x1,t1) (x2,t2) = eqGreen :@ [t1, x1, t2, x2]

> variableParse :: Parsley Token ExTmRN
> variableParse = (|P nameParse|)

> nameParse :: Parsley Token RelName
> nameParse = (|namePartParse : (many $ keyword "." *> namePartParse)|)

> namePartParse :: Parsley Token (String, Offs)
> namePartParse =  (|(,) ident (%keyword "^"%) (| Rel (| read digits |) |)
>                   |(,) ident (%keyword "_"%) (| Abs (| read digits |) |)
>                   |(,) ident ~(Rel 0)
>                   |)


\subsection{Odds and ends}

The |termParse| function produces a parser for terms, given a context, by resolving
in the context all the names in the |InTm String| produced by |bigInTm|.

> termParse :: Entries -> Parsley Token INTM
> termParse es = pFilter (resolve es) bigInTm


> maybeAscriptionParse :: Parsley Token (Maybe InTmRN :<: InTmRN)
> maybeAscriptionParse = do
>     N (tm :? ty) <- pInTm -- ascriptionParse
>     return (Just tm :<: ty)


> iter :: (a -> b -> b) -> [a] -> b -> b
> iter = flip . foldr

> data Size = ArgSize | AppSize | EqSize | AndSize | ArrSize | PiSize | AscSize
>   deriving (Show, Eq, Enum, Bounded, Ord)

> pExTm :: Parsley Token ExTmRN
> pExTm = sizedExTm maxBound

> sizedExTm :: Size -> Parsley Token ExTmRN
> sizedExTm z = specialExTm z <|>
>       (if z > minBound  then pLoop (sizedExTm (pred z)) (moreExTm z)
>                         else bracket Round pExTm)

> sizedInTm :: Size -> Parsley Token InTmRN
> sizedInTm z = specialInTm z <|> (| N (specialExTm z) |) <|>
>       (if z > minBound  then pLoop (sizedInTm (pred z)) (moreInEx z)
>                         else bracket Round pInTm)

> moreInEx :: Size -> InTmRN -> Parsley Token InTmRN
> moreInEx AscSize t =
>   (|N (| (t :?) (%keyword ":"%) pInTm |)|) <|> moreInEx (pred AscSize) t
> moreInEx z (N e) = N <$> moreExTm z e <|> moreInTm z (N e)
> moreInEx z t = moreInTm z t

> pInTm :: Parsley Token InTmRN
> pInTm = sizedInTm maxBound

> specialExTm :: Size -> Parsley Token ExTmRN
> specialExTm ArgSize =
>   (| pFilter findOp ident :@ bracket Round (pSep (keyword ",") pInTm)
>    | P nameParse
>    |)
>   where
>     findOp name = find (\op -> opName op == name) operators
> -- specialExTm AscSize =
>   -- (| sizedInTm (pred AscSize) (%keyword ":"%) :? pInTm |)
> specialExTm z = (|)

> moreExTm :: Size -> ExTmRN -> Parsley Token ExTmRN
> moreExTm AscSize e =
>   (| (N e :?) (%keyword ":"%) pInTm |) <|> moreExTm (pred AscSize) e
> moreExTm AppSize e = (e :$) <$>
>   (| Fst (%keyword "!"%)
>    | Snd (%keyword "-"%)
>    | Out (%keyword "%"%)
>    | A (sizedInTm ArgSize)
>    |)
> moreExTm EqSize e =
>   (|eqG  (pFilter isEqSide (pure (N e))) (%keyword "<->"%)
>          (pFilter isEqSide (sizedInTm (pred EqSize)))
>    |) <|> moreExTm (pred EqSize) e
>   where
>     eqG (y0 :>: t0) (y1 :>: t1) = eqGreen :@ [y0, t0, y1, t1]
> moreExTm z _ = (|)

> specialInTm :: Size -> Parsley Token InTmRN
> specialInTm ArgSize =
>     (|SET (%keyword "*"%) 
>      |PROP (%keyword "#"%)
>      |ABSURD (%keyword "FF"%)
>      |TRIVIAL (%keyword "TT"%)
>      |Q (%keyword "?"%) (ident <|> pure "")
>      |CON (%keyword "@"%) (sizedInTm ArgSize)
>      |TAG (%keyword "`"%) ident
>      |(iter LAV) (%keyword "\\"%) (some ident) (%keyword "->"%) pInTm
>      |id (bracket Square tuple)
>      |ENUMT (bracket Curly (|  (iter (CONSE . TAG)) (pSep (keyword ",") ident)
>                                (| id (%keyword "/"%) pInTm | NILE |)|))
>      |mkNum (|read digits|) (optional $ (keyword "+") *> sizedInTm ArgSize)
>      |id (bracket Round sigma)
>      |)
>   where
>     tuple =
>         (|PAIR (sizedInTm ArgSize) (| id (%keyword "/"%) pInTm | id tuple |)
>          |VOID (% pEndOfStream %)
>          |)
>     sigma = (|mkSigma (optional (ident <* keyword ":")) pInTm sigmaMore
>              |UNIT (% pEndOfStream %)
>              |)
>     sigmaMore = (|id (% keyword ";" %) (sigma <|> pInTm)
>                  |(\p s -> mkSigma Nothing (PRF p) s) (% keyword ":-" %) pInTm sigmaMore
>                  |(\x -> PRF x) (% keyword ":-" %) pInTm
>                  |)
>     mkSigma Nothing s t = C $ Sigma s (L (K t))
>     mkSigma (Just x) s t = C (Sigma s (L (x :. t)))
>     mkNum 0 Nothing = ZE
>     mkNum 0 (Just t) = t
>     mkNum n t = SU (mkNum (n-1) t)
> specialInTm AndSize =
>     (|PRF (%keyword ":-"%) (sizedInTm AndSize)
>      |(MU Nothing) (%keyword "Mu"%) (sizedInTm ArgSize)
>      |)
> specialInTm PiSize =
>     (|(flip iter)  (some (bracket Round (|ident, (%keyword ":"%) pInTm|)))
>                    (| (uncurry PIV) (%keyword "->"%) | (uncurry ALLV) (%keyword "=>"%) |)
>                    pInTm |)
> specialInTm z = (|)

> moreInTm :: Size -> InTmRN -> Parsley Token InTmRN
> moreInTm EqSize t =
>   (| EQBLUE  (pFilter isEqSide (pure t)) (%keyword "=="%)
>              (pFilter isEqSide (sizedInTm (pred EqSize)))
>    |) <|> moreInTm (pred EqSize) t
> moreInTm AndSize s =
>   (| (AND s) (%keyword "&&"%) (sizedInTm AndSize)
>    |)
> moreInTm ArrSize s =
>   (| (ARR s) (%keyword "->"%) (sizedInTm ArrSize)
>    | (IMP s) (%keyword "=>"%) (sizedInTm ArrSize)
>    |)
> moreInTm z _ = (|)

> isEqSide :: InTmRN -> Maybe (InTmRN :>: InTmRN)
> isEqSide (N (t0 :? y0)) = Just (y0 :>: t0)
> isEqSide _ = Nothing
