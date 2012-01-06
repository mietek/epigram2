\section{Cochon Command Lexer}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.CommandLexer where

> import Control.Applicative

> import DisplayLang.Name

> import SourceLang.SourceData
> import SourceLang.Lexer
> import SourceLang.Parx
> import SourceLang.SourceParser

%endif

\pierre{This needs some story.}

\subsection{Tokens}

Because Cochon tactics can take different types of arguments,
we need a tagging mechanism to distinguish them, together
with projection functions.

> data CochonArg = StrArg String 
>                | InArg EpiInTm 
>                | ExArg EpiExTm

<                | SchemeArg DScheme

>                | Optional CochonArg
>                | NoCochonArg
>                | ListArgs [ CochonArg ]
>                | LeftArg CochonArg 
>                | RightArg CochonArg
>                | PairArgs CochonArg CochonArg 
>   deriving Show


\subsection{Tokenizer combinators}

> tokenExTm :: Parx Elt CochonArg
> tokenExTm = (| ExArg epiExTm |)

<  tokenAscription :: Parsley Token CochonArg
< tokenAscription = (| ExArg pAscriptionTC |)

> tokenInTm :: Parx Elt CochonArg
> tokenInTm = (| InArg epiInTm |)

> tokenAppInTm :: Parx Elt CochonArg
> tokenAppInTm = (| InArg smallEpiInTm |)

< tokenName :: Parsley Token CochonArg
< tokenName = (| (ExArg . (::$ []) . DP) nameParse |)

> tokenString :: Parx Elt CochonArg
> tokenString = (| StrArg template |)

< tokenScheme :: Parsley Token CochonArg
< tokenScheme = (| SchemeArg pScheme |)

> tokenOption :: Parx Elt CochonArg -> Parx Elt CochonArg
> tokenOption p = (| Optional (brackElt (Square, Nothing) p) 
>                  | NoCochonArg |)

> tokenEither :: Parx Elt CochonArg -> Parx Elt CochonArg
>                                   -> Parx Elt CochonArg
> tokenEither p q = (| LeftArg p | RightArg q |)

> tokenListArgs :: Parx Elt CochonArg -> Parx Elt CochonArg
> tokenListArgs p = (| ListArgs (gmany p) |) 

> tokenPairArgs :: Parx Elt CochonArg -> Parx Elt () -> 
>                  Parx Elt CochonArg -> Parx Elt CochonArg
> tokenPairArgs p sep q = (| PairArgs p (% sep %) q |)

\subsection{Printers}

> argToStr :: CochonArg -> String
> argToStr (StrArg s) = s

> argToIn :: CochonArg -> EpiInTm
> argToIn (InArg a) = a

> argToEx :: CochonArg -> EpiExTm
> argToEx (ExArg a) = a

> argOption :: (CochonArg -> a) -> CochonArg -> Maybe a
> argOption p (Optional x) = Just $ p x
> argOption _ NoCochonArg = Nothing

> argList :: (CochonArg -> a) -> CochonArg -> [a]
> argList f (ListArgs as) = map f as

> argEither :: (CochonArg -> a) -> (CochonArg -> a) -> CochonArg -> a
> argEither f g (LeftArg a) = f a
> argEither f g (RightArg b) = g b

> argPair :: (CochonArg -> a) -> (CochonArg -> b) -> CochonArg -> (a , b)
> argPair f g (PairArgs a b) = (f a , g b) 
