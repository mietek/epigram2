\subsection{Matching |InDTm|}

To deal with the left-recursive madness, we parse |InDTm| (as well as
|ExDTm|), using two mutually recursive functions: |bigInDTm| and
|littleInDTm|. The basic scheme is the following:

< bigInDTm ::= ...
<           | ...
<           | ...
<           | littleInDTm
< littleInDTm ::= ...
<              | ...
<              | ...
<              | ( bigInDTm )

Where |littleInDTm| contains only the non-ambiguous ``base'' cases:
each of these cases allows us to unambiguously consume tokens. On the
other hand, |bigInDTm| typically contains operations which might go
left, and will do so with |littleInDTm|.


> {-bigInDTm :: Parsley Token InDTmRN
> bigInDTm = 
>     (|id piForallParse
>      |id sigmaParse
>      |id blueEqParse
>      |DPRF (%keyword ":-"%) bigInDTm
>      |(DMU Nothing)  (%keyword "Mu"%) bigInDTm
>      |id (pLoop littleInDTm pLAfter)
>      |DN bigExDTm
>      |)

> littleInDTm :: Parsley Token InDTmRN
> littleInDTm =
>     (|DC ~ Set (%keyword "*"%) 
>      |DC ~ Prop (%keyword "#"%)
>      |DC ~ Absurd (%keyword "FF"%)
>      |DC ~ Trivial (%keyword "TT"%)
>      |DQ (%keyword "?"%) maybeIdent
>      |DCON (%keyword "@"%) littleInDTm
>      |DTAG (%keyword "`"%) ident
>      |id lamParse
>      |id tupleParse
>      |id enumParse
>      |id natParse
>      |DN littleExDTm
>      |id (bracket Round bigInDTm)
>      |)
>   where
>     maybeIdent :: Parsley Token String
>     maybeIdent = ident <|> pure ""

> pLAfter :: InDTmRN -> Parsley Token InDTmRN
> pLAfter s =
>      (| (DARR s) (%keyword "->"%) bigInDTm
>       | (DIMP s) (%keyword "=>"%) bigInDTm
>       | (DAND s) (%keyword "&&"%) bigInDTm
>       |)

> telescope :: Parsley Token [(String, InDTmRN)]
> telescope = some (bracket Round (|ident, (%keyword ":"%) bigInDTm|))

> piForallParse :: Parsley Token InDTmRN
> piForallParse = (|mkPiForall telescope (|(,) ~mkPi (%keyword "->"%) bigInDTm
>                                         |(,) ~mkForall (%keyword "=>"%) bigInDTm|)|)
>     where mkPi (x,s) t = DPI s (DL (x ::. t))
>           mkForall (x,s) t = DALL s (DL (x ::. t))
>           mkPiForall xs (f,t) = foldr f t xs

> arrParse :: Parsley Token InDTmRN
> arrParse = (|DARR littleInDTm (%keyword "->"%) bigInDTm
>             |DIMP littleInDTm (%keyword "=>"%) bigInDTm
>             |)

> lamParse :: Parsley Token InDTmRN
> lamParse = (|(flip $ foldr mkLam) (%keyword "\\"%) (some ident) (%keyword "->"%) bigInDTm|)
>     where mkLam x t = DL (x ::. t)

> sigmaParse :: Parsley Token InDTmRN
> sigmaParse = bracket Round sigma
>     where sigma = (|mkSigma (optional (ident <* keyword ":")) bigInDTm sigmaMore
>                    |DUNIT (% pEndOfStream %)
>                    |)
>           sigmaMore = (|id (% keyword ";" %) (sigma <|> bigInDTm)
>                        |(\p s -> mkSigma Nothing (DPRF p) s) (% keyword ":-" %) bigInDTm sigmaMore
>                        |(\x -> DPRF x) (% keyword ":-" %) bigInDTm
>                        |)
>           mkSigma Nothing s t = DSIGMA s (DL (DK t))
>           mkSigma (Just x) s t = DSIGMA s (DL (x ::. t))
>           

> andParse :: Parsley Token InDTmRN
> andParse = (|(\p q -> DAND p q) littleInDTm 
>                                (%keyword "&&"%) 
>                                littleInDTm|)

> tupleParse :: Parsley Token InDTmRN
> tupleParse = bracket Square tuple 
>     where tuple = (|(\p q -> DPAIR p q) littleInDTm (|id tuple
>                                                    |id (%keyword "/"%) bigInDTm |)
>                    |DC ~ Void (% pEndOfStream %) |)

> enumParse :: Parsley Token InDTmRN
> enumParse = bracket Curly (|(\t -> DC (EnumT t)) enum|)
>     where enum = (|mkEnum (pSep (keyword ",") ident) 
>                           (optional $ (keyword "/" *> bigInDTm))|)
>           mkEnum names Nothing = mkEnum' names DNILE
>           mkEnum names (Just t) = mkEnum' names t
>           mkEnum' = flip $ foldr (\t e -> DCONSE (DTAG t) e) 

> blueEqParse :: Parsley Token InDTmRN
> blueEqParse = (|mkBlueEq parseTerm (%keyword "=="%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleInDTm (%keyword ":"%) littleInDTm|)
>           mkBlueEq (x1,t1) (x2,t2) = DEQBLUE (t1 :>: x1) (t2 :>: x2)

> natParse :: Parsley Token InDTmRN
> natParse = (|mkNum digits (optional $ (keyword "+") *> littleInDTm)|)
>     where mkNum num Nothing = mkNum' (read num) (DC Ze)
>           mkNum num (Just t) = mkNum' (read num) t
>           mkNum' 0 t = t
>           mkNum' n t = mkNum' (n-1) (DC (Su t))

\subsection{Matching |ExDTm|}

> bigExDTm :: Parsley Token ExDTmRN
> bigExDTm = 
>     (|id appParse
>      |id ascriptionParse
>      |id littleExDTm
>      |)


> littleExDTm :: Parsley Token ExDTmRN
> littleExDTm = 
>     (|id operatorParse
>      |id greenEqParse 
>      |id variableParse
>      |id (bracket Round bigExDTm)
>      |)

> appParse :: Parsley Token ExDTmRN
> appParse =
>     pLoop littleExDTm $ \f -> 
>     (|(f ::$) (| (%keyword "!"%) Fst
>                | (%keyword "-"%) Snd
>                | (%keyword "%"%) Out
>                | A littleInDTm|)|)

> ascriptionParse :: Parsley Token ExDTmRN
> ascriptionParse = (| (::?) littleInDTm (%keyword ":"%) bigInDTm |)

> operatorParse :: Parsley Token ExDTmRN
> operatorParse = (|mkOp (pFilter findOp ident) (bracket Round (pSep (keyword ",") bigInDTm))|)
>     where mkOp op args = op ::@ args
>           findOp name = find (\op -> opName op == name) operators 

> greenEqParse :: Parsley Token ExDTmRN
> greenEqParse = (|mkGreenEq parseTerm (%keyword "<->"%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleInDTm (%keyword ":"%) littleInDTm|)
>           mkGreenEq (x1,t1) (x2,t2) = eqGreen ::@ [t1, x1, t2, x2]

> variableParse :: Parsley Token ExDTmRN
> variableParse = (|DP nameParse|) -}


\subsection{Odds and ends}

The |termParse| function produces a parser for terms, given a context, by resolving
in the context all the names in the |InTm String| produced by |bigInTm|.

> {-termParse :: Entries -> Parsley Token INDTM
> termParse es = pFilter (resolve es) bigInDTm -}
