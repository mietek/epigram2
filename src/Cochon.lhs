\section{Cochon (Command-line Interface)}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module Cochon where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import BwdFwd
> import Developments
> import DevLoad
> import Elaborator
> import MissingLibrary
> import Naming
> import Lexer
> import Parsley
> import PrettyPrint
> import Root
> import Rooty
> import Rules
> import Tm hiding (In)
> import TmParse


%endif


Here we have a very basic command-driven interface to the proof state monad.

> cochon :: ProofContext -> IO ()
> cochon loc@(ls, dev) = do
>     let Just me = evalStateT getMotherName loc
>     putStrLn (show (prettyDev (auncles loc) me dev))
>     putStr (showPrompt ls)
>     l <- getLine
>     case parse tokenize l of 
>         Left _ -> putStrLn "No cookie for you!" >> cochon loc
>         Right ts ->
>           case parse (pCommand (auncles loc)) ts of
>               Left _ -> putStrLn "I don't understand!" >> cochon loc
>               Right Quit -> return ()
>               Right c -> case runStateT (evalCommand c) loc of
>                   Just (s, loc') -> do
>                       putStrLn s 
>                       printChanges loc loc'
>                       cochon loc'
>                   Nothing ->  do
>                       putStrLn "I'm sorry, Dave. I'm afraid I can't do that."
>                       cochon loc

> data Nav = InNav | OutNav | Up | Down | Top | Bottom | ModuleNav | Prev | Next | First | Last

> data Command  =  Apply
>               |  Auncles
>               |  DoneCom
>               |  Dump
>               |  Eval INTM
>               |  Give INTM
>               |  Go Nav
>               |  Lambda String
>               |  Make String INTM
>               |  PiBoy String INTM
>               |  Quit
>               |  Select INTM
>               |  Ungawa

> pCommand :: Bwd Entry -> Parsley Token Command
> pCommand es = do
>     x <- ident
>     case x of
>         "apply"    -> (| Apply |)
>         "auncles"  -> return Auncles
>         "bottom"   -> return (Go Bottom)
>         "done"     -> return DoneCom
>         "down"     -> return (Go Down)
>         "dump"     -> return Dump
>         "eval"     -> (| Eval (termParse es) |)
>         "first"    -> return (Go First)
>         "give"     -> (| Give (termParse es) |)
>         "in"       -> return (Go InNav)
>         "lambda"   -> (| Lambda ident |)
>         "last"     -> return (Go Last)
>         "make"     -> (| Make ident (%keyword ":"%) (termParse es) |)
>         "module"   -> return (Go ModuleNav)
>         "next"     -> return (Go Next)
>         "out"      -> return (Go OutNav)
>         "pi"       -> (| PiBoy ident (%keyword ":"%) (termParse es) |)
>         "prev"     -> return (Go Prev)
>         "quit"     -> return Quit
>         "select"   -> (| Select (termParse es) |)
>         "top"      -> return (Go Top)
>         "ungawa"   -> return Ungawa
>         "up"       -> return (Go Up)
>         _          -> empty


> evalCommand :: Command -> ProofState String
> evalCommand Apply           = apply             >> return "Applied."
> evalCommand Auncles         = infoAuncles
> evalCommand DoneCom         = done              >> return "Done."
> evalCommand Dump            = infoDump
> evalCommand (Eval tm)       = infoEval tm       >>= prettyHere
> evalCommand (Give tm)       = give tm           >> return "Thank you."
> evalCommand (Go InNav)      = goIn              >> return "Going in..."
> evalCommand (Go OutNav)     = goOut             >> return "Going out..."
> evalCommand (Go Up)         = goUp              >> return "Going up..."
> evalCommand (Go Down)       = goDown            >> return "Going down..."
> evalCommand (Go Top)        = much goUp         >> return "Going to top..."
> evalCommand (Go Bottom)     = much goDown       >> return "Going to bottom..."
> evalCommand (Go ModuleNav)  = much goOut        >> return "Going to module..."
> evalCommand (Go Prev)       = prevGoal          >> return "Searching for previous goal..."
> evalCommand (Go Next)       = nextGoal          >> return "Searching for next goal..."
> evalCommand (Go First)      = much prevGoal     >> return "Searching for first goal..."
> evalCommand (Go Last)       = much nextGoal     >> return "Searching for last goal..."
> evalCommand (Lambda x)      = lambdaBoy x       >> return "Made lambda boy!"
> evalCommand (Make x ty)     = make (x :<: ty) >> goIn >> return "Appended goal!"
> evalCommand (PiBoy x ty)    = piBoy (x :<: ty)  >> return "Made pi boy!"
> evalCommand (Select x)      = select x          >> return "Selected."
> evalCommand Ungawa          = ungawa            >> return "Ungawa!"



> showPrompt :: Bwd Layer -> String
> showPrompt (_ :< Layer _ (n := _) _ _ _ _)  = showName n ++ " > "
> showPrompt B0        = "> "

> printChanges :: ProofContext -> ProofContext -> IO ()
> printChanges from to = do
>     let Just as = evalStateT getAuncles from
>         Just bs = evalStateT getAuncles to
>     let (lost, gained)  = diff (as <>> F0) (bs <>> F0)
>     if lost /= F0
>         then putStrLn ("Left scope: " ++ showEntriesAbs lost )
>         else return ()
>     if gained /= F0
>        then putStrLn ("Entered scope: " ++ showEntriesAbs gained)
>        else return ()

> diff :: (Eq a, Show a) => Fwd a -> Fwd a -> (Fwd a, Fwd a)
> diff (x :> xs) (y :> ys)
>     | x == y     = diff xs ys
>     | otherwise  = (x :> xs, y :> ys)
> diff xs ys = (xs, ys)
