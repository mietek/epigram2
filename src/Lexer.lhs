\section{Lexer}

I propose to keep the lexical structure fairly simple, with not much by
way of character classification. Every sequence of characters lexes,
but there are `ugly' lexemes which have no part in a valid.

Commas and semicolons always stand alone. Brackets are round, square,
or curly, and you can make fancy brackets by wedging an identifier
between open-and-bar, or bar-and-close without
whitespace. Correspondingly, bar may not be next to an identifier
unless it is part of a bracket. Otherwise, sequences of non-whitespace
are identifiers unless they're keywords.

%------------------------------------------------------------------------
\subsection{Preamble}
%------------------------------------------------------------------------


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeSynonymInstances #-}

%endif

> module Lexer
>  (  Tok(..)     -- structured tokens, nesting brackets and layout
>  ,  Br(..)      -- bracket kinds (infinitely many)
>  ,  tokOut      -- token printer
>  ,  tokenize    -- token snarfer
>  ,  isSpcT      -- test if a token is whitespace
>  ,  brackets    -- test if bracket kinds match: |(blah||..||)| is ok
>  )  where

%if False

> import Control.Applicative
> import Control.Monad.State
> import Data.Char
> import Data.List

%endif

%------------------------------------------------------------------------
\subsection{What are tokens?}
%------------------------------------------------------------------------

We lex into tokens, classified as follows.

> data Tok
>   =  I String  -- identifiers
>   |  Ope Br    -- open brackets
>   |  Clo Br    -- close brackets
>   |  K String  -- keywords
>   |  S Int     -- space
>   |  U String  -- ugly non-lexemes (non-close-bracket bar-starts)
>   |  Com       -- just the comma
>   |  Sem       -- semicolon
>   |  Bar       -- bar (not in another lexeme)
>   |  Eol       -- new line
>                -- tokens used only after bracketing
>   |  B Br [Tok] Br     -- a bracket
>   |  L String [[Tok]]  -- layout introduced by keyword, then lines
>      deriving  (Show, Eq)

We have ordinary and fancy brackets.

> data Br
>   =  Rnd  | RndB String
>   |  Sqr  | SqrB String
>   |  Crl  | CrlB String
>      deriving (Show, Eq)

Here's how to generate the text for a token

> tokOut :: Tok -> String
> tokOut (I s)  = s
> tokOut (Ope b) = case b of
>   Rnd         -> "("
>   RndB s      -> "(" ++ s ++ "|"
>   Sqr         -> "[" 
>   SqrB s      -> "[" ++ s ++ "|"
>   Crl         -> "{"
>   CrlB s      -> "{" ++ s ++ "|"
> tokOut (Clo b) = case b of
>   Rnd         -> ")"
>   RndB s      -> "|" ++ s ++ ")"
>   Sqr         -> "]"
>   SqrB s      -> "|" ++ s ++ "]"
>   Crl         -> "}"
>   CrlB s      -> "|" ++ s ++ "}"
> tokOut (K s)  = s
> tokOut (S i)  = replicate i ' '
> tokOut (U s)  = s
> tokOut Eol     = "\n"


%------------------------------------------------------------------------
\subsection{Tokenizing}
%------------------------------------------------------------------------

The lexing process is almost a classic unfold. We generate a list of
tokens labelled with their starting column. The slightly contextual
behaviour of bar means we need a running repair.

> tokenize :: String -> [(Int, Tok)]
> tokenize = fixUp . unfoldr (runStateT (|gets fst, tokIn|)) . (,) 0

We check for spaces and specials first. We detect bar-starts, but not
bar-ends.

> tokIn :: L Tok
> tokIn = (| S (| length (some (ch ' ')) |)
>          | Ope  {ch '('} (| RndB (spa isOrd) {ch '|'} | Rnd |)
>          | Ope  {ch '['} (| SqrB (spa isOrd) {ch '|'} | Sqr |)
>          | Ope  {ch '{'} (| CrlB (spa isOrd) {ch '|'} | Crl |)
>          | Clo  ~ Rnd {ch ')'}
>          | Clo  ~ Sqr {ch ']'}
>          | Clo  ~ Crl {ch '}'}
>          | Clo  {ch '|'} (| (flip ($)) (spa isOrd)
>              (| RndB {ch ')'} | SqrB {ch ']'} | CrlB {ch '}'} |) |)
>          | U    (| ch '|' : some (chk isOrd cha) |)
>          | Bar  {ch '|'}
>          | Com  {ch ','}
>          | Sem  {ch ';'}
>          | Eol  {chk isNL cha}
>          | ik   (some (chk isOrd cha))
>          |)
>  where   ik s = if elem s keywords then K s else I s

However, we can repair the problem by checking the output sequence for
bars in the wrong place.

> fixUp :: [(Int, Tok)] -> [(Int, Tok)]
> fixUp [] = []
> fixUp ((i, I s)  : (_, Bar)  : its) = fixUp $ (i, U (s ++ "|"))  : its
> fixUp ((i, K s)  : (_, Bar)  : its) = fixUp $ (i, U (s ++ "|"))  : its
> fixUp ((i, U s)  : (_, Bar)  : its) = fixUp $ (i, U (s ++ "|"))  : its
> fixUp ((i, I s)  : (_, U t)  : its) = fixUp $ (i, U (s ++ t))    : its
> fixUp ((i, K s)  : (_, U t)  : its) = fixUp $ (i, U (s ++ t))    : its
> fixUp ((i, U s)  : (_, U t)  : its) = fixUp $ (i, U (s ++ t))    : its
> fixUp (x : xs) = x : fixUp xs


%------------------------------------------------------------------------------
\subsection{Classifiers, odds and ends}
%------------------------------------------------------------------------------

> isOrd :: Char -> Bool
> isOrd c = not (isSpace c || elem c ",;()[]{}|")
>
> isNL :: Char -> Bool
> isNL b = elem b "\r\n"

> keywords :: [String]
> keywords = ["where"]

> isSpcT :: Tok -> Bool
> isSpcT (S _)  = True
> isSpcT Eol    = True
> isSpcT _      = False

> brackets :: Br -> Br -> Bool
> brackets (RndB _)  (RndB "")  = True
> brackets (SqrB _)  (SqrB "")  = True
> brackets (CrlB _)  (CrlB "")  = True
> brackets o         c          = o == c

%------------------------------------------------------------------------
\subsection{Lexer monad}
%------------------------------------------------------------------------

It's an off-the-peg monad. But why do I have to roll my own gubbins?

> type L = StateT (Int, String) Maybe
>
> instance Alternative L where
>   empty = StateT $ \ is -> empty
>   p <|> q = StateT $ \ is -> runStateT p is <|> runStateT q is
>
> instance Applicative L where
>   pure = return
>   (<*>) = ap

We'll need some bits and pieces.

> cha :: L Char
> cha = StateT moo where
>   moo (i, []) = Nothing
>   moo (i, c : s)
>     |  isNL c = Just (c, (0, s))
>     |  c == '\t' -- unwind tabs
>     =  if mod i 8 == 7 then Just (' ', (i + 1, s))
>                        else Just (' ', (i + 1, c : s))
>     |  otherwise = Just (c, (i + 1, s))
>
> chk :: (t -> Bool) -> L t -> L t
> chk p l = do t <- l ; if p t then return t else empty
>
> ch :: Char -> L Char
> ch c = chk (== c) cha
>
> spa :: (Char -> Bool) -> L String
> spa p = (| chk p cha : spa p | [] |)
