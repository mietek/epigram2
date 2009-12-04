\section{TmParse}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module TmParse where

> import Control.Applicative
> import Data.Foldable hiding (foldr)
> import Data.Traversable

> import Lexer
> import Parsley
> import Tm

%endif

\subsection{Matching terminal symbols}

> keyword :: String -> Parsley Token ()
> keyword s = tokenEq (Keyword s)

> ident :: Parsley Token String
> ident = pFilter filterIdent nextToken
>     where filterIdent (Identifier s) = Just s
>           filterIdent _ = Nothing

> bracket :: Bracket -> Parsley Token x -> Parsley Token x
> bracket bra p = pFilter filterBra nextToken
>     where filterBra (Brackets bra' toks) | bra == bra' = 
>               either (\_ ->Nothing) Just $ parse p toks
>           filterBra _ = Nothing

\subsection{Matching |InTm|}

> bigTmIn :: Parsley Token (InTm String)
> bigTmIn = 
>     (|id piParse
>      |id arrParse
>      |id sigmaParse
>      |id littleTmIn
>      |)

> littleTmIn :: Parsley Token (InTm String)
> littleTmIn =
>     (|C ~ Set (%keyword "*"%) 
>      |C ~ Prop (%keyword "#"%) 
>      |id lamParse
>      |id (bracket Round bigTmIn)
>      |)



> piParse :: Parsley Token (InTm String)
> piParse = (|(flip $ foldr mkPi) piVars (%keyword "->"%) bigTmIn|)
>     where mkPi (x,s) t = PI s (L (x :. t))
>           piVars = many (bracket Round (|ident, (%keyword ":"%) bigTmIn|))

> arrParse :: Parsley Token (InTm String)
> arrParse = (|mkArr littleTmIn (%keyword "->"%) bigTmIn|)
>     where mkArr s t = ARR s t

> lamParse :: Parsley Token (InTm String)
> lamParse = (|(flip $ foldr mkLam) (%keyword "\\"%) (some ident) (%keyword "->"%) bigTmIn|)
>     where mkLam x t = L (x :. t)


> sigmaParse :: Parsley Token (InTm String)
> sigmaParse = bracket Round sigma
>     where sigma = (|mkSigma (optional (ident <* keyword ":")) bigTmIn sigmaMore
>                    |C ~ Unit (% pEndOfStream %)
>                    |)
>           sigmaMore = (|id (% keyword ";" %) (sigma <|> bigTmIn)

%if false

>  --                      |(\p s -> mkSigma ) (% keyword ":-" %) bigTmIn sigmaMore

%endif

>                        |(\x -> PRF x) (% keyword ":-" %) bigTmIn
>                        |)
>           mkSigma Nothing s t = C $ Sigma s (L (K t))
>           mkSigma (Just x) s t = C (Sigma s (L (x :. t)))
>           

