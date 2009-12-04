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

\subsection{Matching |InTm|}

> bigTmIn :: Parsley Token (InTm String)
> bigTmIn = 
>     (|id piParse
>      |id arrParse
>      |id sigmaParse
>      |id tupleParse
>      |id enumParse
>      |id forallParse
>      |id blueEqParse
>      |(\p q -> AND p q) littleTmIn (%keyword "&&"%) littleTmIn
>      |N bigTmEx
>      |id littleTmIn
>      |)

> littleTmIn :: Parsley Token (InTm String)
> littleTmIn =
>     (|C ~ Set (%keyword "*"%) 
>      |C ~ Prop (%keyword "#"%)
>      |C ~ Absurd (%keyword "FF"%)
>      |C ~ Trivial (%keyword "TT"%)
>      |id lamParse
>      |(\t -> PRF t) (%keyword ":-"%) littleTmIn
>      |(\t -> CON t) (%keyword "@"%) littleTmIn
>      |id (bracket Round bigTmIn)
>      |)

> bigTmEx :: Parsley Token (ExTm String)
> bigTmEx = 
>     (|(:?) littleTmIn (%keyword ":"%) bigTmIn
>      |id variableParse
>      |)

> variableParse :: Parsley Token (ExTm String)
> variableParse = (|mkVar (pExtent 
>                          (|(:) nameParse 
>                                (many $ keyword "." *> nameParse)|))|)
>     where mkVar (str,_) = P $ show =<< str
>           nameParse = (|(,) ident
>                             (optional $ keyword "^" *> digits)|)

> telescope :: Parsley Token [(String, InTm String)]
> telescope = some (bracket Round (|ident, (%keyword ":"%) bigTmIn|))

> piParse :: Parsley Token (InTm String)
> piParse = (|(flip $ foldr mkPi) telescope (%keyword "->"%) bigTmIn|)
>     where mkPi (x,s) t = PI s (L (x :. t))

> forallParse :: Parsley Token (InTm String)
> forallParse = (|(flip $ foldr mkForall) telescope (%keyword "=>"%) bigTmIn|)
>     where mkForall (x,s) t = ALL s (L (x :. t))

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
>                        |(\p s -> mkSigma Nothing (PRF p) s) (% keyword ":-" %) bigTmIn sigmaMore
>                        |(\x -> PRF x) (% keyword ":-" %) bigTmIn
>                        |)
>           mkSigma Nothing s t = C $ Sigma s (L (K t))
>           mkSigma (Just x) s t = C (Sigma s (L (x :. t)))
>           

> tupleParse :: Parsley Token (InTm String)
> tupleParse = bracket Square tuple 
>     where tuple = (|(\p q -> PAIR p q) littleTmIn (|id tuple
>                                                    |id (%keyword "/"%) bigTmIn |)
>                    |C ~ Void (% pEndOfStream %) |)

> enumParse :: Parsley Token (InTm String)
> enumParse = bracket Curly enum
>     where enum = (|mkEnum (pSep (keyword ",") ident) 
>                           (optional $ (keyword "/" *> bigTmIn))|)
>           mkEnum names Nothing = mkEnum' names NILE
>           mkEnum names (Just t) = mkEnum' names t
>           mkEnum' = flip $ foldr (\t e -> CONSE (TAG t) e) 

> blueEqParse :: Parsley Token (InTm String)
> blueEqParse = (|mkBlueEq parseTerm (%keyword "=="%) parseTerm|)
>     where parseTerm = bracket Round (|(,) littleTmIn (%keyword ":"%) littleTmIn|)
>           mkBlueEq (x1,t1) (x2,t2) = EQBLUE (t1 :>: x1) (t2 :>: x2)