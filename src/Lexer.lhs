\section{Lexer}

The lexical structure is extremely simple. The reason is that Cochon
being an interactive theorem prover, its inputs will be
straightforward, 1-dimension terms. Being interactive, our user is
also more interested in knowing where she did a mistake, rather than
having the ability to write terms in 3D.

We want to recognize ``valid'' identifiers, and keywords, with all of
this structures by brackets. Interestingly, we only consider correctly
paired brackets: we never use left-over brackets, and it is much
simpler to work with well-parenthesized expressions when parsing
terms. Brackets are round, square, or curly, and you can make fancy
brackets by wedging an identifier between open-and-bar, or
bar-and-close without whitespace. Sequences of non-whitespace are
identifiers unless they're keywords.


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeSynonymInstances #-}

> module Lexer (Token(..),
>               Bracket(..),
>               tokenize) where

> import Control.Monad
> import Control.Applicative
> import Data.List

> import Parsley

%endif

%------------------------------------------------------------------------
\subsection{What are tokens?}
%------------------------------------------------------------------------

We lex into tokens, classified as follows.

> data Token
>   =  Identifier String                    -- identifiers
>   |  Keyword String                       -- keywords
>   |  Brackets Bracket [Token]             -- bracketted tokens
>      deriving Eq

Brackets are the structuring tokens. We have:

> data Bracket
>   =  Round  | RoundB String    -- |(| or |(foo|||
>   |  Square | SquareB String   -- |[| or |[foo|||
>   |  Curly  | CurlyB String    -- |{| or |{foo|||
>      deriving Eq

As we are very likely to |show| our tokens all too often, let us
implement a pretty |Show| instance on tokens.

> instance Show Token where
>     show (Identifier s) = s
>     show (Keyword s) = s
>     show (Brackets bra toks) = 
>       showOpenB bra ++ (show =<< toks) ++ showCloseB bra 
>           where showOpenB Round = "("
>                 showOpenB Square = "["
>                 showOpenB Curly = "{"
>                 showOpenB (RoundB s) = "(" ++ s ++ "|"
>                 showOpenB (SquareB s) = "[" ++ s ++ "|"
>                 showOpenB (CurlyB s) = "{" ++ s ++ "|"
>                 showCloseB Round = ")"
>                 showCloseB Square = "]"
>                 showCloseB Curly = "}"
>                 showCloseB (RoundB s) = "|" ++ s ++ ")"
>                 showCloseB (SquareB s) = "|" ++ s ++ "]"
>                 showCloseB (CurlyB s) = "|" ++ s ++ "}"


\subsection{Lexer}

We implement the tokenizer as a |Parsley| on |Char|s. That's a cheap
solution for what we have to do. The previous implementation was
running other the string of characters, wrapped in a |StateT| monad
transformer. 

\question{What was the benefit of a |StateT| lexer, as we have a
          parser combinator library at hand?}

A token is either a bracketted expression, a keyword, or, failing all
that, an identifier. Hence, we can recognize a token with the
following parser:

> parseToken :: Parsley Char Token
> parseToken = (|id parseBrackets
>               |id parseKeyword 
>               |id parseIdent 
>               |)

Tokenizing an input string then simply consists in matching a bunch of
token separated by spaces. For readability, we are also glutton in
spaces the user may have put before and after the tokens.

> tokenize :: Parsley Char [Token]
> tokenize = spaces *> pSep spaces parseToken <* spaces

In the following, we implement these combinators in turn: |spaces|,
|parseIdent|, |parseKeyword|, and |parseBrackets|.

\subsubsection{Lexing spaces}

A space is one of the following character:

> space :: String
> space = " \n\r"

So, we look for |many| of them:

> spaces :: Parsley Char ()
> spaces = (many $ tokenFilter (flip elem space)) *> pure ()

\subsubsection{Parsing words}

As an intermediary step before keyword, identifier, and brackets, let
us introduce a parser for words. A word is any non-empty string of
characters that doesn't include a space or a bracketting symbol. In
|Parsley|, this translates to:

> parseWord :: Parsley Char String
> parseWord = some $ tokenFilter (\t -> not $ elem t $ space ++ bracket)

As we are at it, we can test for word equality, that is build a parser
matching a given word:

> wordEq :: String -> Parsley Char ()
> wordEq word = pFilter filter parseWord
>     where filter s | s == word = Just () 
>                    | otherwise = Nothing

Equipped with |parseWord| and |wordEq|, the following lexers win a
level of abstraction, working on words instead of characters.


\subsubsection{Lexing identifiers}

Hence, parsing an identifier simply consists in successfully parsing a
word and saying ``oh! it's an |Identifier|''.

> parseIdent = fmap Identifier parseWord

\subsubsection{Lexing keywords}

Keywords are slightly more involved. A keyword is one of the following
thing. Don't forget to extend this list if you use new keywords in the
grammar!

> keywords :: [String]
> keywords = [ "\\", "->", ":", "*", "#"
>            , "==", "<->", "&&", ";", ":-" ]

To implement |parseKeyword|, this is simply a matter of filtering by
words that can be found in the |keywords| list.

> parseKeyword :: Parsley Char Token
> parseKeyword = pFilter (\t -> fmap Keyword $ find (t ==) keywords) parseWord

\subsubsection{Lexing brackets}

Brackets, open and closed, are one of the following.

> openBracket, closeBracket, bracket :: String
> openBracket = "([{"
> closeBracket = "}])"
> bracket = "|" ++ openBracket ++ closeBracket

Parsing brackets, as you would expect, requires a monad: we're not
context-free my friend. This is slight variation around the |pLoop|
combinator. 

First, we use |parseOpenBracket| to match an opening bracket, and get
it's code. Thanks to this code, we can already say that we hold a
|Brackets|. We are left with tokenizing the content of the bracket, up
to parsing the corresponding closing bracket. 

Parsing the closing bracket is made slightly more complex by the
presence of fancy brackets: we have to match the fancy name of the
opening bracket with the one of the closing bracket.

> parseBrackets :: Parsley Char Token
> parseBrackets = do
>   bra <- parseOpenBracket
>   (|(Brackets bra)
>      (|id tokenize (%parseCloseBracket bra %) |) |)
>     where parseOpenBracket :: Parsley Char Bracket
>           parseOpenBracket = (|id (% tokenEq '(' %)
>                                     (|RoundB parseWord (% tokenEq '|' %)
>                                      |Round (% spaces %)|)
>                               |id (% tokenEq '[' %)
>                                     (|SquareB parseWord (% tokenEq '|' %)
>                                      |Square (% spaces %)|)
>                               |id (% tokenEq '{' %)
>                                     (|CurlyB parseWord (% tokenEq '|' %)
>                                      |Curly (% spaces %)|)
>                               |)                                                        
>           parseCloseBracket :: Bracket -> Parsley Char ()
>           parseCloseBracket Round = tokenEq ')' 
>           parseCloseBracket Square = tokenEq ']'
>           parseCloseBracket Curly = tokenEq '}'
>           parseCloseBracket (RoundB s) = matchBracketB s ')'
>           parseCloseBracket (SquareB s) = matchBracketB s ']'
>           parseCloseBracket (CurlyB s) = matchBracketB s '}'
>           parseBracket x = tokenFilter (flip elem x)
>           matchBracketB s bra = (|id ~ () (% tokenEq '|' %) 
>                                           (% wordEq s %) 
>                                           (% tokenEq bra %) |)

