\section{TmParse}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module TmParse where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> import Lexer
> import Parsley
> import Tm

%endif

> weeTmIn :: P Tok (InTm String)
> weeTmIn =
>   (|id (bra Rnd bigTmIn)
>    |C ~ Set {key "Set"}
>    |mkL {key "\\"} (some (spc *> idf)) {key "->"} bigTmIn
>    |N weeTmEx
>    |)
>  where
>    mkL [] t = t
>    mkL ("_" : xs) t = L (K (mkL xs t))
>    mkL (x : xs) t = L (x :. mkL xs t)

> bigTmIn :: P Tok (InTm String)
> bigTmIn =
>     (|mkPi
>       (bra Rnd (pSep (pad (teq Sem)) (|idf, {key ":"} bigTmIn|)))
>       {key "->"} bigTmIn
>      |) <|> (pLoop (|N bigTmEx | id weeTmIn|) $ \ i ->
>     (|Arr ~ i {key "->"} bigTmIn
>      |))
>   where
>     mkPi []             t = t
>     mkPi ((x, s) : xs)  t = C (Pi s (L (x :. mkPi xs t)))

> weeTmEx :: P Tok (ExTm String)
> weeTmEx =
>   (|P idf
>    |id (bra Rnd bigTmEx)
>    |id (bra Rnd (|bigTmIn :? {key ":"} bigTmIn|))
>    |)

> bigTmEx :: P Tok (ExTm String)
> bigTmEx = pLoop weeTmEx $ \ e -> spc *>
>   (|(e :-) (|A weeTmIn|)
>    |)

> spc :: P Tok ()
> spc = (|() {many (tok isSpcT)}|)

> pad :: P Tok x -> P Tok x
> pad p = (|id {spc} p {spc}|)

> bra :: Br -> P Tok x -> P Tok x
> bra b p = grok inside next where
>   inside (Bra o ts c) | o == b  = parse (pad p) ts
>   inside _                      = Nothing

> idf :: P Tok String
> idf = grok g next where
>   g (Idf s)  = Just s
>   g _        = Nothing

> key :: String -> P Tok ()
> key s = pad (teq (Key s))
