\section{Main}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import Control.Monad.State
> import System
> import System.IO
> import System.Console.GetOpt

> import Kit.BwdFwd

> import ProofState.Edition.ProofContext

> import Tactics.Information

> import Cochon.DevLoad
> import Cochon.Cochon

%endif



The following flags can be passed to the executable:

> data Options = LoadFile FilePath
>              | CheckFile FilePath
>              | PrintFile FilePath
>              | Interactive
>              | Help
>
> options :: [OptDescr Options]
> options = [ Option ['l'] ["load"]  (ReqArg LoadFile "FILE")   "Load the development"
>           , Option ['c'] ["check"] (ReqArg CheckFile "FILE")  "Check the development"
>           , Option ['p'] ["print"] (ReqArg PrintFile "FILE")  "Print the development"
>           , Option ['i'] ["interactive"] (NoArg Interactive)  "Interactive mode"
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
>           "Typing 'Pig --load FILE' has the same effect as 'Pig FILE'.\n" ++
>           "If no input file is given, Pig starts in the empty context.\n" ++
>           "Given the file name '-', Pig will read from standard input.\n\n" ++
>           "Options: "

Finally, here is the |main|. Its role is simply to call |getOpt| and
switch over the result. It's not extremely cute but there is no magic
either.

> main :: IO ()
> main = do
>        argv <- System.getArgs
>        case getOpt RequireOrder options argv of
>          -- Help:
>          (Help : _, _, [])            -> do
>            putStrLn $ usageInfo message options
>          -- Load a development:
>          (LoadFile file : _, _, [])   -> do
>            loadDev file
>          -- Check a development:
>          (CheckFile file : _, _, [])  -> do
>            withFile file (\loc -> do
>                                   validateDevelopment loc
>                                   putStrLn "Loaded.")
>          -- Print a development:
>          (PrintFile file : _, _, [])  -> do
>            withFile file printTopDev
>          -- Load a development (no flag provided):
>          ([],(file:[]),[])            -> do
>            loadDev file
>          -- Empty development:
>          (Interactive : _,[],[])      -> do
>            cochon emptyContext            
>          -- Empty development:
>          ([],[],[])                   -> do
>            cochon emptyContext            
>          -- Error:
>          (_,_,errs)                   -> do
>            ioError (userError (concat errs ++
>                                usageInfo message options))
>  where
>    withFile :: String -> (Bwd ProofContext -> IO a) -> IO a
>    withFile "-" g = devLoad' (Just stdin) (return []) >>= g
>    withFile file g = devLoad file >>= g

>    loadDev :: String -> IO ()
>    loadDev file = withFile file cochon'

>    printTopDev :: Bwd ProofContext -> IO ()
>    printTopDev (_ :< loc) = do
>        let Right s = evalStateT prettyProofState loc
>        putStrLn s

