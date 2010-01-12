\section{Main}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import Control.Monad.State
> import Data.Foldable hiding (elem)
> import Data.Maybe
> import System


> import BwdFwd
> import Cochon
> import Compiler
> import DevLoad
> import Elaborator
> import Lexer
> import Parsley
> import PrettyPrint
> import ProofState

%endif

> message = "Epigram version (suc n)\n" ++
>           "-----------------------\n" ++
>           "Usage:\n" ++
>           "\tPig [input file] [options]\n\n" ++
>           "If no input file is given, Pig starts in the empty context\n\n" ++
>           "Options: --help             Display this message\n"      

> main :: IO ()
> main = do
>     args <- getArgs
>     let opts = processOpts args
>     if Help `elem` opts  then  putStrLn message >> exitWith ExitSuccess
>                          else  return ()
>     case getOpt inFile opts of
>         Just fn -> do
>             inp <- readFile fn
>             locs <- devLoad inp    
>             cochon' locs
>         Nothing -> cochon emptyContext


> data Option = InFile FilePath | Help
>    deriving (Eq, Show)

> processOpts [] = []
> processOpts ("--help":epicopts) = Help : []
> processOpts (fname:xs) = InFile fname : processOpts xs

> inFile (InFile n) = Just n
> inFile _ = Nothing

> help Help = Just message
> help _ = Nothing

> getOpt f opts = case catMaybes (map f opts) of
>                   [n] -> Just n
>                   _ -> Nothing