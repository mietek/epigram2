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
> import Data.Foldable hiding (concatMap, concat)
> import Data.Monoid

> import Tm
> import Developments
> import BwdFwd
> import Features

%endif

> type CName = String

> data CompileFn = Comp [CName] FnBody 

> data FnBody = Var CName
>             | App FnBody [FnBody]
>             | Case FnBody [FnBody] (Maybe FnBody) -- scrutinee, branches, default
>             | Proj FnBody Int   -- project from a tuple
>             | CTag Int          -- any tag
>             | STag FnBody       -- for Su
>             | Tuple [FnBody]
>             | Lazy FnBody       -- evaluate body lazily
>             | Ignore            -- anything we can't inspect. Types, basically.

Where to look for support files. We'll need this to be a bit cleverer later. Only interested
in epic/support.e for now (which is a good place to implement operators, for example).

> libPath = [".", "./epic"]

Given a list of names and definitions, and the top level function to evaluate,
write out an executable. This will evaluate the function and dump the result.
Also take a list of extra options to give to epic (e.g. for keeping intermediate code, etc)

> output :: Bwd (CName, CompileFn) -> CName -> FilePath -> String -> IO ()
> output defs mainfn outfile epicopts =
>    do (epicFile, eh) <- tempfile
>       fold $ fmap ((hPutStrLn eh).codegen) defs
>       support <- readLibFile libPath "support.e"
>       hPutStrLn eh support
>       hPutStrLn eh (mainDef mainfn)
>       hClose eh
>       let cmd = "epic " ++ epicFile ++ " -o " ++ outfile ++ " " ++ epicopts
>       exit <- system cmd
>       if (exit /= ExitSuccess) 
>         then fail "EPIC FAIL"
>         else return ()

> arglist = concat.(intersperse ",")

Things which are convertible to Epic code

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
>     codegen (Lazy t) = "lazy(" ++ codegen t ++ ")"
>     codegen Ignore = "42"

> mainDef :: CName -> String
> mainDef m = "main () -> Unit = __dumpData(" ++ m ++ "())"

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

Convert a term into the body of a function (need to add the argument names elsewhere).

> class MakeBody t where
>     makeBody :: t -> FnBody

We'll need to convert whatever representation was used for names into a name usable in C:

> class CNameable n where
>     cname :: n -> String

> instance Show t => CNameable [(String, t)] where
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
>     makeBody (tm :? ty) = makeBody tm
>     makeBody (L (K tm)) = App (Var "__const") [makeBody tm]
>     makeBody _ = error "Please don't do that"

Lots of canonical things are just there for the typechecker, and we don't care about them.
So we'll just ignore everything that isn't otherwise explained.

> instance CNameable n => MakeBody (Can (Tm {In, p} n)) where
>     import <- CanCompile
>     makeBody (Con t) = makeBody t
>     makeBody _ = Ignore

> instance CNameable n => MakeBody (Tm {Ex, p} n, Elim (Tm {In, p} n)) where
>     makeBody (f, A arg) = appArgs f [makeBody arg]
>        where appArgs :: Tm {d, p} n -> [FnBody] -> FnBody
>              appArgs (f :$ (A a)) acc = appArgs f (makeBody a:acc)
>              appArgs f acc = App (makeBody f) acc
>     makeBody (f, Out) = makeBody f
>     import <- ElimCompile

Operators will, in many cases, just compile to an application of a function we write
by hand in Epic - see epic/support.e

> instance CNameable n => MakeBody (Op, [Tm {In, p} n]) where
>     makeBody (Op name arity _ _, args) 
>          = case (name, map makeBody args) of
>                import <- OpCompile
>                _ -> error ("Unknown operator" ++ show name)

> compileModule :: Dev Bwd -> Bwd (CName, CompileFn)
> compileModule (entries, Module, _) = fmap compileEntry entries

> compileEntry (E name _ (Girl LETG (entries, tip, _)) _) 
>       = (cname name, collectArgs [] entries tip)

> collectArgs :: [REF] -> Entries -> Tip -> CompileFn
> collectArgs acc B0 (Defined tm _) = Comp (map cname acc) (makeBody tm)
> collectArgs acc (bs :< E name _ (Boy _) _) tip = collectArgs (name:acc) bs tip

%if False

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

> program = B0 :< (cname plus, plusFn) :< (cname test, testFn)

> testOut = output program (cname test) "testout"

%endif