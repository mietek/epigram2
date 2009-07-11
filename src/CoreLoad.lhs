\section{CoreLoad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module CoreLoad where

> import Control.Monad
> import Control.Monad.State
> import Control.Applicative
> import Data.Char

> import BwdFwd
> import Tm
> import Lexer
> import Parsley
> import TmParse
> import Core

%endif

> data Offs = Rel Int | Abs Int | None deriving Show

> noffer :: Char -> Bool
> noffer c = not (elem c ".^_")

> offs :: P Char Offs
> offs =
>   (|Abs {teq '_'} (|read (some (tok isDigit))|)
>    |Rel {teq '^'} (|read (some (tok isDigit))|)
>    |None
>    |)

> relName :: P Char [(String,Offs)]
> relName = pSep (teq '.') (|some (tok noffer), offs|)

> load :: [[Tok]] -> Construct [[Tok]]
> load [] = (|[]|)
> load (ts@(Key "--" : _) : tss) = (|(ts :) (load tss)|)

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap
