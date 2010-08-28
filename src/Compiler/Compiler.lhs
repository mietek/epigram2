\section{Compiler}

This module uses Epic (@git clone git://github.com/edwinb/EpiVM.git@, 
or download from @http://github.com/edwinb/EpiVM@) to
generate an executable from a collection of supercombinator definitions.

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Compiler.Compiler where

> import System.Environment
> import System.IO
> import System
> import Char
> import List
> import Control.Monad.State
> import Data.Traversable
> import Control.Applicative

> import NameSupply.NameSupply

> import Evidences.Tm
> import Evidences.Mangler

> import ProofState.Structure.Developments

> import Features.Features ()

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Compiler.OpDef

%endif


\subsection{Representing Epic syntax}

A |CName|, as one might expect, is a string name usable in C (or Epic). It
should only contain alphanumeric characters and underscores.

> type CName = String

The |CNameable| typeclass describes how to convert the Epigram representation
of names into |CName|s.

> class Show n => CNameable n where
>     cname :: n -> CName

> instance Show t => CNameable [(String, t)] where
>     cname = concatMap (\ (n,i) -> "_" ++ concatMap decorate n ++ "_" ++ show i)
>         where decorate '_' = "__"
>               decorate x | isAlphaNum x = [x]
>                          | otherwise = '_':(show (fromEnum x)) ++ "_"

> instance CNameable REF where
>     cname (x := d) = cname x


> data CompileFn = Comp [CName] FnBody 

> data FnBody = Var CName
>             | App FnBody [FnBody]
>             | Case FnBody [FnBody] (Maybe FnBody) -- scrutinee, branches, default
>             | Proj FnBody Int   -- project from a tuple
>             | CTag Int          -- any tag
>             | STag FnBody       -- for Su
>             | DTag FnBody       -- decrement (for jump tables)
>             | Let CName FnBody FnBody
>             | Tuple [FnBody]
>             | Lazy FnBody       -- evaluate body lazily
>             | Missing String    
>             | Ignore            -- anything we can't inspect. Types, basically.
>             | Error String
>    deriving Show


\subsection{Compiling functions}

The |MakeBody| typeclass describes how to convert a term into the body of a 
function (need to add the argument names elsewhere).

> class MakeBody t where
>     makeBody :: t -> FnBody


> instance (CNameable n) => MakeBody (Tm {d,p} n) where
>     makeBody (C can)       = makeBody can
>     makeBody (N t)         = makeBody t
>     makeBody (P x)         = Var (cname x)
>     makeBody (tm :$ elim)  = makeBody (tm, elim)
>     makeBody (op :@ args)  = makeBody (op, args)
>     makeBody (tm :? ty)    = makeBody tm
>     makeBody (L (K tm))    = App (Var "__const") [makeBody tm]
>     makeBody x = error ("Please don't do this: makeBody " ++ show x)


Lots of canonical things are just there for the typechecker, and we don't care
about them. So we'll just ignore everything that isn't otherwise explained.

> instance CNameable n => MakeBody (Can (Tm {In, p} n)) where
>     import <- CanCompile
>     makeBody (Con t)  = makeBody t
>     makeBody _        = Ignore

> instance CNameable n => MakeBody (Tm {Ex, p} n, Elim (Tm {In, p} n)) where
>     makeBody (f, A arg) = appArgs f [makeBody arg]
>        where appArgs :: Tm {d, p} n -> [FnBody] -> FnBody
>              appArgs (f :$ (A a)) acc = appArgs f (makeBody a:acc)
>              appArgs f acc = App (makeBody f) acc
>     makeBody (f, Out) = makeBody f
>     import <- ElimCompile

Operators will, in many cases, just compile to an application of a function we
write by hand in the Epic support file @epic/support.e@.
\question{Why do we not report unknown operators sooner?}

> instance CNameable n => MakeBody (Op, [Tm {In, p} n]) where
>     makeBody (Op name arity _ _ _, args) 
>          = case (name, map makeBody args) of
>                import <- OpCompile
>                _ -> Lazy (Error ("Unknown operator" ++ show name))
>                     -- |error ("Unknown operator" ++ show name)|


\subsection{Code generation}

> arglist = concat . (intersperse ",")

The |CodeGen| typeclass describes things that are convertible to Epic code.

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
>     codegen (DTag n) = codegen n ++ "-1"
>     codegen (Let x v sc) = "(let " ++ x ++ ":Any = " ++ codegen v
>                            ++ " in " ++ codegen sc ++ ")"
>     codegen (Tuple xs) = "[" ++ arglist (map codegen xs) ++ "]"
>     codegen (Lazy t) = "lazy(" ++ codegen t ++ ")"
>     codegen (Missing m) = "error \"Missing definition " ++ m ++ "\""
>     codegen Ignore = "42"
>     codegen (Error s) = "error " ++ show s


\subsection{Flattening and lambda-lifting}

> makeFns :: [(Name, Bwd Name, FnBody)] -> [(CName, CompileFn)]
> makeFns xs = map (\ (n, args, tm) -> 
>                  (cname n, Comp (map cname (trail args)) tm)) xs
>              ++ opGen

> flatten :: ParamKind -> Name -> Bwd Name -> Dev Fwd -> 
>            [(Name, Bwd Name, FnBody)]
> flatten b     ma del (Dev F0 Module _ _) = []
> flatten ParamLam  ma del (Dev F0 (Unknown _) _ _) = [(ma, del, Missing (cname ma))]
> flatten ParamLam  ma del (Dev F0 (Defined tm _) _ _) = 
>     let (t, (_, defs)) = runState (lambdaLift ma del (fmap refName tm)) 
>                                   (ma ++ [("lift",0)],[]) in
>            (ma, del, makeBody t) : defs
> flatten ParamAll  ma del (Dev F0 _ _ _) = [(ma, del, Ignore)]
> flatten ParamPi   ma del (Dev F0 _ _ _) = [(ma, del, Ignore)]
> flatten _         ma del dev@(Dev {devEntries = EPARAM (x := _) _ b _ _ :> es}) =
>     flatten b ma (del :< x) dev{devEntries=es}
> flatten b         ma del dev@(Dev {devEntries = EDEF (her := _) _ _ herDev _ _ :> es}) = 
>     flatten ParamLam her del herDev ++ flatten b ma del dev{devEntries=es}

Lambda lifting: every lambda which is not at the top level is lifted out as a
new top level definition. We keep track of the new top level functions we've
added, and the next available name,

> type LiftState = (Name, [(Name, Bwd Name, FnBody)])

> nextName xs = reverse (nextName' (reverse xs))
>    where nextName' ((nm,i):xs) = (nm,i+1):xs

> addDef :: Name -> (Bwd Name, InTm Name) -> 
>           State LiftState ()
> addDef nm (args, t) = do (n, fns) <- get
>                          put (n, (nm, args, makeBody t):fns)

> newName :: State LiftState Name
> newName = do (nm, fns) <- get
>              put (nextName nm, fns)
>              return (nextName nm)

When we encounter a lambda, we create a new top level definition with all
the arguments we've collected so far, plus the arguments to the lambda.
Then replace the lambda with an application of the new function to all
the names in scope.

> lambdaLift :: Name -> Bwd Name -> Tm {d,TT} Name -> 
>               State LiftState (Tm {d,TT} Name)
> lambdaLift nm args l@(L (x :. t)) = lift args args l where
>     lift :: Bwd Name -> Bwd Name -> (InTm Name) -> 
>             State LiftState (InTm Name)
>     lift tlargs args (L sc@(x :. t)) 
>       = let name = nm ++ [(x,bwdLength args)] in
>             lift tlargs (args :< name) (underScope sc name)
>     lift tlargs args t = do t' <- lambdaLift nm args t
>                             name <- newName
>                             addDef name (args, t')
>                             return (N (apply (P name) tlargs))
>     apply f B0 = f
>     apply f (args :< a) = apply f args :$ (A (N (P a)))

Everything else is boring traversal of the term.

> lambdaLift nm args (L (K t)) = do t' <- lambdaLift nm args t
>                                   return (L (K t'))
> lambdaLift nm args (C can) = (|C (traverse (lambdaLift nm args) can) |)
> lambdaLift nm args (N t) = (|N (lambdaLift nm args t) |)
> lambdaLift nm args (op :@ as) = 
>      (| ~op :@ (traverse (lambdaLift nm args) as) |)
> lambdaLift nm args (t :$ el) = 
>      (| lambdaLift nm args t :$ traverse (lambdaLift nm args) el |)
> lambdaLift nm args (v :? t) = 
>      (| lambdaLift nm args v :? (| (error "Can't happen") |) |)
> lambdaLift nm args tm = (| tm |)


\subsection{Invoking compilation}

Where to look for support files. We'll need this to be a bit cleverer later.
Only interested in @epic/support.e@ for now (which is a good place to implement
operators, for example).

> libPath = [".", "./epic"]


The |compileCommand| takes the name of a main term to evaluate, a (forward)
development containing the definitions, and an output file name. It calls
Epic to produce an executable that evaluates the term, and returns whether
compilation was successful.

> compileCommand :: Name -> Dev Fwd -> String -> IO Bool
> compileCommand mainName dev outfile = do
>     let flat = flatten ParamLam [] B0 dev
>     output (makeFns flat) (cname mainName) outfile ""


Given a list of names and definitions, and the top level function to evaluate,
write out an executable. This will evaluate the function and dump the result.
Also take a list of extra options to give to Epic (e.g. for keeping intermediate
code).

> output :: [(CName, CompileFn)] -> CName -> FilePath -> String -> IO Bool
> output defs mainfn outfile epicopts =
>    do (epicFile, eh) <- tempfile
>       Prelude.mapM_ ((hPutStrLn eh) . codegen) defs
>       support <- readLibFile libPath "support.e"
>       hPutStrLn eh support
>       hPutStrLn eh (mainDef mainfn)
>       hClose eh
>       let cmd = "epic -checking 1 " ++ epicFile ++ " -o " ++ outfile ++ " " ++ epicopts
>       exit <- system cmd
>       return (exit == ExitSuccess)

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

> mainDef :: CName -> String
> mainDef m = "main () -> Unit = __dumpData(" ++ m ++ "())"


We add a Cochon tactic to invoke the compiler.

> import -> CochonTactics where
>   : CochonTactic
>         {  ctName = "compile"
>         ,  ctParse = (|(|(B0 :<) tokenName|) :< tokenString|)
>         ,  ctIO = (\ [ExArg (DP r ::$ []), StrArg fn] (locs :< loc) -> do
>             let  Right dev = evalStateT getAboveCursor loc
>                  Right (n := _) = evalStateT (resolveDiscard r) loc
>             b <- compileCommand n (reverseDev dev) fn
>             putStrLn (if b then "Compiled." else "EPIC FAIL")
>             return (locs :< loc)
>           )
>         ,  ctHelp = "compile <name> <file> - compiles the proof state with <name> as the main term to be evalauted, producing a binary called <file>."
>         }


\subsection{Operator definitions}

Generating operator definitions from descriptions

> makeOpCompile :: String -> OpDef -> CompileFn
> makeOpCompile opname op = mkOp argNames [] op where
>     mkOp (x:xs) args (Arg fn) 
>         = mkOp xs (args ++ [aname x]) 
>                   (fn (NP (aname x := fakeRef)))
>     mkOp (x:xs) args (ConArg fn) 
>         = mkOp xs (args ++ [aname x]) 
>                   (fn (NP (aname x := fakeRef)))
>     mkOp ns args (Body b) = Comp (map cname args) (mkDef ns b)

>     mkDef _ (Val v) = makeBody v
>     mkDef (x:xs) (Dec v scope)
>            = Let (cname (aname x)) (DTag (makeBody v)) 
>                  (mkDef xs (scope (NP (aname x := fakeRef))))
>     mkDef xs (IsZero v z s)
>            = Case (mkDef xs v) [mkDef xs z] (Just (mkDef xs s))

>     aname x = [(opname, 0), x]
>     fakeRef = error "Made up reference in makeOpCompile"

> argNames = map (\i -> ("x",i)) [1..]

> opList :: [(String, OpDef)]
> opList = (
>   import <- OpGenerate
>   [])

> opGen :: [(CName, CompileFn)]
> opGen = map (\ (n, def) -> ("__"++n, makeOpCompile n def)) opList


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

> program = [(cname plus, plusFn), (cname test, testFn)]

> testOut = output program (cname test) "testout"

%endif
