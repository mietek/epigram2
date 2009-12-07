\section{TmParse}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module TmParse where

> import Control.Applicative
> import Data.Foldable hiding (foldr)
> import Data.Traversable

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
defined in Section~\section{sec:language}.

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

> bigInTm :: Parsley Token (InTm String)
> bigInTm = 
>     (|id piParse
>      |id arrParse
>      |id sigmaParse
>      |id forallParse
>      |id blueEqParse
>      |id andParse
>      |N bigExTm
>      |id littleInTm
>      |)

> littleInTm :: Parsley Token (InTm String)
> littleInTm =
>     (|C ~ Set (%keyword "*"%) 
>      |C ~ Prop (%keyword "#"%)
>      |C ~ Absurd (%keyword "FF"%)
>      |C ~ Trivial (%keyword "TT"%)
>      |id lamParse
>      |(\t -> PRF t) (%keyword ":-"%) littleInTm
>      |(\t -> CON t) (%keyword "@"%) littleInTm
>      |id tupleParse
>      |id enumParse
>      |N littleExTm
>      |id (bracket Round bigInTm)
>      |)



> telescope :: Parsley Token [(String, InTm String)]
> telescope = some (bracket Round (|ident, (%keyword ":"%) bigInTm|))

> piParse :: Parsley Token (InTm String)
> piParse = (|(flip $ foldr mkPi) telescope (%keyword "->"%) bigInTm|)
>     where mkPi (x,s) t = PI s (L (x :. t))

> forallParse :: Parsley Token (InTm String)
> forallParse = (|(flip $ foldr mkForall) telescope (%keyword "=>"%) bigInTm|)
>     where mkForall (x,s) t = ALL s (L (x :. t))

> arrParse :: Parsley Token (InTm String)
> arrParse = (|mkArr littleInTm (%keyword "->"%) bigInTm|)
>     where mkArr s t = ARR s t

> lamParse :: Parsley Token (InTm String)
> lamParse = (|(flip $ foldr mkLam) (%keyword "\\"%) (some ident) (%keyword "->"%) bigInTm|)
>     where mkLam x t = L (x :. t)

> sigmaParse :: Parsley Token (InTm String)
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

> andParse :: Parsley Token (InTm String)
> andParse = (|(\p q -> AND p q) littleInTm 
>                                (%keyword "&&"%) 
>                                littleInTm|)

> tupleParse :: Parsley Token (InTm String)
> tupleParse = bracket Square tuple 
>     where tuple = (|(\p q -> PAIR p q) littleInTm (|id tuple
>                                                    |id (%keyword "/"%) bigInTm |)
>                    |C ~ Void (% pEndOfStream %) |)

> enumParse :: Parsley Token (InTm String)
> enumParse = bracket Curly enum
>     where enum = (|mkEnum (pSep (keyword ",") ident) 
>                           (optional $ (keyword "/" *> bigInTm))|)
>           mkEnum names Nothing = mkEnum' names NILE
>           mkEnum names (Just t) = mkEnum' names t
>           mkEnum' = flip $ foldr (\t e -> CONSE (TAG t) e) 

> blueEqParse :: Parsley Token (InTm String)
> blueEqParse = (|mkBlueEq parseTerm (%keyword "=="%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleInTm (%keyword ":"%) littleInTm|)
>           mkBlueEq (x1,t1) (x2,t2) = EQBLUE (t1 :>: x1) (t2 :>: x2)


\subsection{Matching |ExTm|}

> bigExTm :: Parsley Token (ExTm String)
> bigExTm = 
>     (|id ascriptionParse
>      |id operatorParse
>      |(:$) littleExTm (|A bigInTm|)
>      |id greenEqParse 
>      |id littleExTm
>      |)


> littleExTm :: Parsley Token (ExTm String)
> littleExTm = 
>     (|id variableParse |)

> ascriptionParse :: Parsley Token (ExTm String)
> ascriptionParse = (| (:?) littleInTm (%keyword ":"%) bigInTm |)

> operatorParse :: Parsley Token (ExTm String)
> operatorParse = (|mkOp (pFilter findOp ident) (bracket Round (pSep (keyword ",") bigInTm))|)
>     where mkOp op args = op :@ args
>           findOp name = find (\op -> opName op == name) operators 

> greenEqParse :: Parsley Token (ExTm String)
> greenEqParse = (|mkGreenEq parseTerm (%keyword "<->"%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleInTm (%keyword ":"%) littleInTm|)
>           mkGreenEq (x1,t1) (x2,t2) = eqGreen :@ [t1, x1, t2, x2]

> variableParse :: Parsley Token (ExTm String)
> variableParse = (|mkVar (pExtent 
>                          (|(:) nameParse 
>                                (many $ keyword "." *> nameParse)|))|)
>     where mkVar (str,_) = P $ crushToken =<< str
>           nameParse = (|(,) ident
>                             (optional $ keyword "^" *> digits)|)

\subsection{Parsing Terms}

The |termParse| function produces a parser for terms, given a context, by resolving
in the context all the names in the |InTm String| produced by |bigInTm|.

> termParse :: Bwd Entry -> Parsley Token INTM
> termParse es = pFilter (resolve es) bigInTm