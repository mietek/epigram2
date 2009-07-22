\section{Compiler}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Compiler where

> import System.Environment
> import System.IO
> import System
> import Char
> import List

> import Tm

%endif

> data CompileFn = Comp [Name] FnBody 

> data FnBody = Var Name
>             | App FnBody [FnBody]
>             | Case FnBody [FnBody] (Maybe FnBody)
>             | Proj FnBody Int
>             | CTag Int
>             | Tuple [FnBody]
>             | Ignore

Where to look for support files:

> libPath = [".", "./epic"]

Given a list of names and definitions, and the top level function to evaluate,
write out an executable. This will evaluate the function and dump the result.

> output :: [(Name, CompileFn)] -> Name -> FilePath -> IO ()
> output defs mainfn outfile =
>    do (epicFile, eh) <- tempfile
>       mapM_ (hPutStrLn eh) (map codegen defs) 
>       support <- readLibFile libPath "support.e"
>       hPutStrLn eh support
>       hPutStrLn eh (mainDef mainfn)
>       hClose eh
>       exit <- system $ "epic " ++ epicFile ++ " -o " ++ outfile
>       if (exit /= ExitSuccess) 
>         then fail "EPIC FAIL"
>         else return ()

> arglist = concat.(intersperse ",")

Things which are convertible to epic code

> class CodeGen x where
>     codegen :: x -> String

> instance CodeGen (Name, CompileFn) where
>     codegen (n, def) = cname n ++ " " ++ codegen def

> instance CodeGen CompileFn where
>     codegen (Comp args body) = "(" ++ arglist (map showarg args) ++ ") -> Data = " ++ 
>                                codegen body
>        where 
>              showarg n = cname n ++ ":Data"

> instance CodeGen FnBody where
>     codegen (Var x) = cname x
>     codegen (App f args) = codegen f ++ "(" ++ arglist (map codegen args) ++ ")"
>     codegen (Case sc opts def)
>             = "case " ++ codegen sc ++ " of { " ++
>               concat (intersperse " | " 
>                       (addDefault def (zipWith genOpt (map show [0..]) opts)))
>               ++ " } "
>       where addDefault Nothing opts = opts
>             addDefault (Just def) opts = opts ++ [genOpt "Default" def]
>             genOpt o c = o ++ " -> " ++ codegen c

>     codegen (Proj f i) = "(" ++ codegen f ++ "!" ++ show i ++ ")"
>     codegen (CTag i) = show i
>     codegen (Tuple xs) = "[" ++ arglist (map codegen xs) ++ "]"
>     codegen Ignore = "42"

> mainDef :: Name -> String
> mainDef m = "main () -> Unit = dumpData(" ++ cname m ++ "())"

> cname :: Name -> String
> cname = concatMap (\ (n,i) -> "_" ++ concatMap decorate n ++ "_" ++ show i)
>   where decorate '_' = "__"
>         decorate x | isAlphaNum x = [x]
>                    | otherwise = '_':(show (fromEnum x)) ++ "_"

> tempfile :: IO (FilePath, Handle)
> tempfile = 
>    do env <- environment "TMPDIR"
>       let dir = case env of
>                    Nothing -> "/tmp"
>                    (Just d) -> d
>       openTempFile dir "Pig"

> environment :: String -> IO (Maybe String)
> environment x = catch (do e <- getEnv x
>                           return (Just e))
>                       (\_ -> return Nothing)

> readLibFile :: [FilePath] -> FilePath -> IO String
> readLibFile xs x = tryReads (map (\f -> f ++ "/" ++ x) (".":xs))
>    where tryReads [] = fail $ "Can't find " ++ x
>          tryReads (x:xs) = catch (readFile x)
>                                  (\e -> tryReads xs)





A simple test case

> x = [("x",0)]
> y = [("y",0)]
> plus = [("plus", 0)]
> test = [("test", 0)]

> zero = Tuple [CTag 0, Tuple []]
> suc x = Tuple [CTag 1, Tuple [x]]

> one = suc zero
> two = suc one

> plusFn = Comp [x,y] plusBody
> plusBody = Case (Proj (Var x) 0)
>                [Var y,
>                  suc (App (Var plus) [Proj (Proj (Var x) 1) 0, Var y])] Nothing

> testFn = Comp [] (App (Var plus) [two,two])

> program = [(plus, plusFn), (test, testFn)]

> testOut = output program test "testout"
