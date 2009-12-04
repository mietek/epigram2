\section{Main}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import Data.Foldable
> import Data.Maybe
> import System


> import BwdFwd
> import Parsley
> import Lexer
> import Compiler

%endif

> message = "Epigram version (suc n)\n" ++
>           "-----------------------\n" ++
>           "Usage:\n" ++
>           "\tPig [input file] [options]\n\n" ++
>           "If no input file is given, Pig functions as a filter\n\n" ++
>           "Options: -o <name>          Output an executable with name <name>\n" ++
>           "         --help             Display this message\n" ++
>           "         --epic <options>   Send further options to epic\n" ++
>           "         --cochon           Run the cochon interface\n"


%if False

That's dead code, Jim.

< pipe :: String -> String
< pipe = foldMap (foldMap tokOut) . snd . devLoad . layout . tokenize

< pipeT :: String -> String
< pipeT = (++ "\n") . show . fst . devLoad . layout . tokenize

< main :: IO ()
< main = interact pipeT

%endif

Read input, compile to 'epi.out'

> main :: IO ()
> main = do  args <- getArgs
>            let opts = processOpts args
>            inp <- case getOpt inFile opts of
>                     Just n -> readFile n
>                     Nothing -> getContents
>            case getOpt help opts of
>                     Just m -> do putStrLn m; exitWith ExitSuccess
>                     _ -> return ()

This was the old behaviour:

>            let dev = undefined -- FIX (or not):  (fst . devLoad . tokenize) inp
>            -- FIX (or not): print dev

Pull out the definitions, and, if the -o flag has been used, output an executable
which evaluates the last definition in the development.             

>            let defs = compileModule dev
>            let mainName = fst (Data.Foldable.foldl (\ _ t -> t) undefined defs)
>            case getOpt outFile opts of
>              Just n -> output defs mainName n (maybe "" id (getOpt epic opts))
>              _ -> return ()

If the --cochon flag has been used, run the interactive interface:

>            case getOpt cochonOpt opts of
>              Just ()  -> cochon (B0, dev)
>              _        -> return ()

> data Option = InFile FilePath | OutFile FilePath | Epic String | Help | Cochon
>    deriving Show

> processOpts [] = []
> processOpts ("-o":fname:xs) = OutFile fname : processOpts xs
> processOpts ("--epic":epicopts) = Epic (Prelude.concat epicopts) : []
> processOpts ("--help":epicopts) = Help : []
> processOpts ("--cochon":xs) = Cochon : processOpts xs
> processOpts (fname:xs) = InFile fname : processOpts xs

> outFile (OutFile n) = Just n
> outFile _ = Nothing

> inFile (InFile n) = Just n
> inFile _ = Nothing

> epic (Epic stuff) = Just stuff
> epic _ = Nothing

> help Help = Just message
> help _ = Nothing

> cochonOpt Cochon = Just ()
> cochonOpt _ = Nothing

> getOpt f opts = case catMaybes (map f opts) of
>                   [n] -> Just n
>                   _ -> Nothing