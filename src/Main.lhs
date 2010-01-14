\section{Main}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import System
> import System.Console.GetOpt

> import DevLoad
> import Cochon
> import ProofState

%endif



The following flags can be passed to the executable:

> data Options = LoadFile FilePath
>              | CheckFile FilePath
>              | Help
>
> options :: [OptDescr Options]
> options = [ Option ['l'] ["load"]  (ReqArg LoadFile "FILE")   "Load the development"
>           , Option ['c'] ["check"] (ReqArg CheckFile "FILE")  "Check the development"
>           , Option ['h'] ["help"]  (NoArg Help)               "Help! Help!"
>           ]

Where |CheckFile| simply loads a development and terminates, whereas
|LoadFile| drops to an interactive interface awaiting user's commands.

In case of error or explicit call to help, we display this nifty
message:

> message = "Epigram version (suc n)\n" ++
>           "-----------------------\n" ++
>           "Usage:\n" ++
>           "\tPig [options] [input file]\n\n" ++
>           "Typing 'Pig --load FILE' has the same effect as 'Pig FILE'\n" ++
>           "If no input file is given, Pig starts in the empty context\n\n" ++
>           "Options: "

Finally, here is the |main|. Its role is simply to call |getOpt| and
switch over the result. It's not extremely cute but there is no magic
either.

> main :: IO ()
> main = do
>        argv <- System.getArgs
>        case getOpt RequireOrder options argv of
>          -- Help:
>          (Help : _, _, []) -> do
>            putStrLn $ usageInfo message options
>          -- Load a development:
>          (LoadFile file : _, _, []) -> loadDev file
>          -- Check a development:
>          (CheckFile file : _, _, []) -> do
>            development <- readFile file
>            locs <- devLoad development
>            putStrLn "Loaded."
>          -- Load a development (no flag provided):
>          ([],(file:[]),[]) -> loadDev file
>          -- Empty development:
>          ([],[],[]) -> cochon emptyContext            
>          -- Error:
>          (_,_,errs) -> do
>            ioError (userError (concat errs ++
>                                usageInfo message options))
>     where loadDev file = do
>            development <- readFile file
>            locs <- devLoad development
>            cochon' locs

