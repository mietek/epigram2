> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import Data.Foldable
> import Data.Maybe
> import System

> import Lexer
> import Layout
> import CoreLoad
> import Compiler

> message = "Epigram version (suc n)\n" ++
>           "-----------------------\n" ++
>           "Usage:\n" ++
>           "\tPig <input file> [options]\n\n" ++
>           "Options: -o <name>          Output an executable with name <name>\n" ++
>           "         --epic <options>   Send further options to epic\n"

> pipe :: String -> String
> pipe = foldMap (foldMap tokOut) . snd . coreLoad . layout . tokenize

> pipeT :: String -> String
> pipeT = (++ "\n") . show . fst . coreLoad . layout . tokenize

> main :: IO ()
> -- main = interact pipeT

> main = cmain

Read input, compile to 'epi.out'

> cmain :: IO ()
> cmain = do args <- getArgs
>            (infile, opts) <- usage args
>            inp <- readFile infile
>            let dev = (fst . coreLoad . layout . tokenize) inp
>            print dev
>            let defs = compileModule dev
>            let mainName = fst (Data.Foldable.foldl (\ _ t -> t) undefined defs)
>            case getOpt outFile opts of
>              Just n -> output defs mainName n (maybe "" id (getOpt epic opts))
>              _ -> return ()

> data Option = OutFile FilePath | Epic String

> usage :: [String] -> IO (FilePath, [Option])
> usage (file:xs) = return (file, processOpts xs)
> usage _ = do putStrLn message
>              exitWith (ExitFailure 1)

> processOpts [] = []
> processOpts ("-o":fname:xs) = OutFile fname : processOpts xs
> processOpts ("--epic":epicopts) = Epic (Prelude.concat epicopts) : []

> outFile (OutFile n) = Just n
> outFile _ = Nothing

> epic (Epic stuff) = Just stuff
> epic _ = Nothing

> getOpt f opts = case catMaybes (map f opts) of
>                   [n] -> Just n
>                   _ -> Nothing