\section{Compiler}

This module uses Epic (darcs get http://www-fp.cs.st-and.ac.uk/~eb/darcs/EpiVM) to
generate an executable from a collection of supercombinator definitions.

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
> import Features

%endif

> type CName = String

> data CompileFn = Comp [CName] FnBody 

> data FnBody = Var CName
>             | App FnBody [FnBody]
>             | Case FnBody [FnBody] (Maybe FnBody)
>             | Proj FnBody Int
>             | CTag Int
>             | STag FnBody 
>             | Tuple [FnBody]
>             | Ignore

Where to look for support files:

> libPath = [".", "./epic"]

Given a list of names and definitions, and the top level function to evaluate,
write out an executable. This will evaluate the function and dump the result.

> output :: [(CName, CompileFn)] -> CName -> FilePath -> IO ()
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

> instance CodeGen (CName, CompileFn) where
>     codegen (n, def) = n ++ " " ++ codegen def

> instance CodeGen CompileFn where
>     codegen (Comp args body) = "(" ++ arglist (map showarg args) ++ ") -> Data = " ++ 
>                                codegen body
>        where 
>              showarg n = n ++ ":Data"

> instance CodeGen FnBody where
>     codegen (Var x) = x
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
>     codegen (STag n) = "1+" ++ codegen n
>     codegen (Tuple xs) = "[" ++ arglist (map codegen xs) ++ "]"
>     codegen Ignore = "42"

> mainDef :: CName -> String
> mainDef m = "main () -> Unit = dumpData(" ++ m ++ "())"

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

> class MakeBody t where
>     makeBody :: t -> FnBody

> class CNameable n where
>     cname :: n -> String

> instance CNameable Name where
>     cname = concatMap (\ (n,i) -> "_" ++ concatMap decorate n ++ "_" ++ show i)
>         where decorate '_' = "__"
>               decorate x | isAlphaNum x = [x]
>                          | otherwise = '_':(show (fromEnum x)) ++ "_"

> instance CNameable REF where
>     cname (x := d) = cname x

> instance CNameable n => MakeBody (Tm {d,p} n) where
>     makeBody (C can) = makeBody can
>     makeBody (N t) = makeBody t
>     makeBody (P x) = Var (cname x)
>     makeBody (tm :$ elim) = makeBody (tm, elim)
>     makeBody (op :@ args) = makeBody (op, args)
>     makeBody (tm :? ty) = Ignore
>     makeBody _ = error "Please don't do that"

> instance CNameable n => MakeBody (Can (Tm {In, p} n)) where
>     makeBody Set = Ignore
>     makeBody (Pi _ _) = Ignore
>     import <- CanCompile
>     makeBody _ = Ignore

> instance CNameable n => MakeBody (Tm {Ex, p} n, Elim (Tm {In, p} n)) where
>     import <- ElimCompile
>     makeBody (arg, A f) = appArgs f [makeBody arg]
>        where appArgs :: Tm {d, p} n -> [FnBody] -> FnBody
>              appArgs (a :$ (A f)) acc = appArgs f (makeBody a:acc)
>              appArgs f acc = App (makeBody f) acc

> instance CNameable n => MakeBody (Op, [Tm {In, p} n]) where
>     makeBody (Op name arity _ _, args) 
>          = case (name, map makeBody args) of
>                import <- OpCompile
>                _ -> error "Unknown operator"

A simple test case

> x,y,plus,test :: Name

> x = [("x",0)]
> y = [("y",0)]
> plus = [("plus", 0)]
> test = [("test", 0)]

> zero = Tuple [CTag 0, Tuple []]
> suc x = Tuple [CTag 1, Tuple [x]]

> one = suc zero
> two = suc one

> plusFn = Comp [cname x,cname y] plusBody
> plusBody = Case (Proj (Var (cname x)) 0)
>              [Var (cname y),
>               suc (App (Var (cname plus)) [Proj (Proj (Var (cname x)) 1) 0, Var (cname y)])]
>              Nothing

> testFn = Comp [] (App (Var (cname plus)) [two,two])

> program = [(cname plus, plusFn), (cname test, testFn)]

> testOut = output program (cname test) "testout"
