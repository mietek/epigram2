\section{Parser}
\label{sec:SourceLang.Parser}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module SourceLang.Parser where

> import Control.Applicative
> import Data.Traversable

> import Evidences.Tm
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Lexer
> import DisplayLang.TmParse

> import SourceLang.Structure

> import Kit.Parsley

%endif

For the moment, we set aside the question of how to get an |EpiDoc Lexed|
and just explain how to parse the terms inside. Parsing documents has yet to be
implemented: we should first lex the file to a string of tokens,

< lex :: String -> Either String [Token]

then organise the tokens into a list of constructions,

< firstParse :: [Token] -> Either String (EpiDoc Lexed)

and finally invoke the following to parse the terms within the constructions.
(We might also want a better representation of parse errors.)

> parseEpiDoc :: EpiDoc Lexed -> Either String (EpiDoc Parsed)
> parseEpiDoc = traverse parseConstr

> parseConstr :: Construction Lexed -> Either String (Construction Parsed)
> parseConstr = traverse parseTerm
>   where
>     parseTerm :: String -> Either String (String, DInTmRN)
>     parseTerm s = case parse tokenize s of
>         Left err -> Left (show err)
>         Right toks -> case parse pDInTm toks of
>             Left err -> Left (show err)
>             Right tm -> return (s, tm)
