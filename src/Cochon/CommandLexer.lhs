\section{Cochon Command Lexer}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.CommandLexer where

> import Control.Applicative

> import Kit.Parsley

> import DisplayLang.Lexer
> import DisplayLang.TmParse
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme

%endif

\pierre{This needs some story.}

\subsection{Tokens}

Because Cochon tactics can take different types of arguments,
we need a tagging mechanism to distinguish them, together
with projection functions.

> data CochonArg = StrArg String 
>                | InArg DInTmRN 
>                | ExArg DExTmRN
>                | SchemeArg (Scheme DInTmRN)
>                | Optional CochonArg
>                | NoCochonArg
>                | ListArgs [ CochonArg ]
>                | LeftArg CochonArg 
>                | RightArg CochonArg
>                | PairArgs CochonArg CochonArg 
>   deriving Show


\subsection{Tokenizer combinators}

> tokenExTm :: Parsley Token CochonArg
> tokenExTm = (| ExArg pDExTm |)

> tokenAscription :: Parsley Token CochonArg
> tokenAscription = (| ExArg pAscriptionTC |)

> tokenInTm :: Parsley Token CochonArg
> tokenInTm = (| InArg pDInTm |)

> tokenAppInTm :: Parsley Token CochonArg
> tokenAppInTm = (| InArg (sizedDInTm AppSize) |)

> tokenName :: Parsley Token CochonArg
> tokenName = (| (ExArg . (::$ []) . DP) nameParse |)

> tokenString :: Parsley Token CochonArg
> tokenString = (| StrArg ident |)

> tokenScheme :: Parsley Token CochonArg
> tokenScheme = (| SchemeArg pScheme |)

> tokenOption :: Parsley Token CochonArg -> Parsley Token CochonArg
> tokenOption p = (| Optional (bracket Square p) 
>                  | NoCochonArg |)

> tokenEither :: Parsley Token CochonArg -> Parsley Token CochonArg
>                                        -> Parsley Token CochonArg
> tokenEither p q = (| LeftArg p | RightArg q |)

> tokenListArgs :: Parsley Token CochonArg -> Parsley Token () -> Parsley Token CochonArg
> tokenListArgs p sep = (| ListArgs (pSep sep p) |) 

> tokenPairArgs :: Parsley Token CochonArg -> Parsley Token () -> 
>                  Parsley Token CochonArg -> Parsley Token CochonArg
> tokenPairArgs p sep q = (| PairArgs p (% sep %) q |)

\subsection{Printers}

> argToStr :: CochonArg -> String
> argToStr (StrArg s) = s

> argToIn :: CochonArg -> DInTmRN
> argToIn (InArg a) = a

> argToEx :: CochonArg -> DExTmRN
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
