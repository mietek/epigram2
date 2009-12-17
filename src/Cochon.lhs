\section{Cochon (Command-line Interface)}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module Cochon where

> import Compiler
> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.Foldable
> import Data.List
> import Data.Traversable
> import System.IO (hFlush, stdout)

> import BwdFwd
> import Developments
> import Elaborator
> import MissingLibrary
> import Naming
> import Lexer
> import Parsley
> import PrettyPrint
> import ProofState
> import Root
> import Rooty
> import Rules
> import Tm hiding (In)
> import TmParse


%endif

Here we have a very basic command-driven interface to the proof state monad.

> cochon :: ProofContext -> IO ()
> cochon loc = cochon' loc "Hello!"

> cochon' :: ProofContext -> String -> IO ()
> cochon' loc@(ls, dev) msg = do
>     --putStrLn (show loc)
>     let Right s = evalStateT prettyProofState loc
>     putStrLn s
>     putStrLn msg
>     putStr (showPrompt ls)
>     hFlush stdout
>     l <- getLine
>     case parse tokenize l of 
>         Left pf -> cochon' loc ("Tokenize failure: " ++ describePFailure pf id)
>         Right ts ->
>           case parse pCommand ts of
>               Left pf -> cochon' loc ("Parse failure: " ++ describePFailure pf (intercalate " " . map crushToken))
>               Right Quit -> return ()
>               Right (Compile rn fn) -> do
>                   let  Right aus = evalStateT getAuncles loc
>                        mn = resolve aus rn
>                   case mn of
>                       Just (N (P (n := _))) -> do
>                           let mloc' = execStateT gimme loc
>                           case mloc' of
>                               Left ss -> error ("gimme failed: " ++ unlines ss)
>                               Right loc' -> do
>                                   let Right dev = evalStateT getDev loc'
>                                   compileCommand n (reverseDev' dev) fn
>                                   cochon' loc "Compiled."
>                       Nothing -> cochon' loc "Can't resolve."
>               Right c -> case runStateT (doCommand c) loc of
>                   Right (s, loc') -> do
>                       printChanges loc loc'
>                       cochon' loc' s
>                   Left ss ->
>                       cochon' loc (unlines ("I'm sorry, Dave. I'm afraid I can't do that.":ss))

> describePFailure :: PFailure a -> ([a] -> String) -> String
> describePFailure (PFailure (ts, fail)) f = (case fail of
>     Abort        -> "parser aborted."
>     EndOfStream  -> "end of stream."
>     EndOfParser  -> "end of parser."
>     Expect t     -> "expected " ++ f [t] ++ "."
>   ) ++ (if length ts > 0
>        then ("\nSuccessfully parsed: ``" ++ f ts ++ "''.")
>        else "")

> data NavC  =  InC | OutC
>            |  Up | Down | Top | Bottom 
>            |  RootC
>            |  Prev | Next | First | Last
>     deriving Show

> data Command x  =  Apply
>                 |  Auncles
>                 |  DoneC
>                 |  Dump
>                 |  Elaborate x
>                 |  Compile x String
>                 |  Give x
>                 |  Go NavC
>                 |  Infer x
>                 |  Jump x
>                 |  Lambda String
>                 |  Make String (Maybe x :<: x)
>                 |  ModuleC String
>                 |  PiBoy String x
>                 |  Quit
>                 |  Select x
>                 |  Show x
>                 |  Ungawa
>     deriving Show

> instance Traversable Command where
>     traverse f Apply                = (| Apply |)
>     traverse f Auncles              = (| Auncles |)
>     traverse f (Compile x fn)       = (| Compile (f x) ~fn |)
>     traverse f DoneC                = (| DoneC |)
>     traverse f Dump                 = (| Dump |)
>     traverse f (Elaborate x)        = (| Elaborate (f x) |)
>     traverse f (Give x)             = (| Give (f x) |)
>     traverse f (Go d)               = (| (Go d) |)
>     traverse f (Infer x)            = (| Infer (f x) |)
>     traverse f (Jump x)             = (| Jump (f x) |)
>     traverse f (Lambda s)           = (| (Lambda s) |)
>     traverse f (Make s (md :<: x))  = (| (Make s) (| (traverse f md) :<: (f x) |) |)
>     traverse f (ModuleC s)          = (| (ModuleC s) |)
>     traverse f (PiBoy s x)          = (| (PiBoy s) (f x) |)
>     traverse f Quit                 = (| Quit |)
>     traverse f (Select x)           = (| Select (f x) |)
>     traverse f (Show x)             = (| Show (f x) |)
>     traverse f Ungawa               = (| Ungawa |)

> instance Functor Command where
>     fmap = fmapDefault

> instance Foldable Command where
>     foldMap = foldMapDefault

> pCommand :: Parsley Token (Command InTmRN)
> pCommand = do
>     x <- ident
>     case x of
>         "apply"    -> (| Apply |)
>         "auncles"  -> (| Auncles |)
>         "bottom"   -> (| (Go Bottom) |)
>         "compile"  -> (| Compile (| N variableParse |) pFileName |)
>         "done"     -> (| DoneC |)
>         "down"     -> (| (Go Down) |)
>         "dump"     -> (| Dump |)
>         "elab"     -> (| Elaborate bigInTm |)
>         "first"    -> (| (Go First) |)
>         "give"     -> (| Give bigInTm |)
>         "in"       -> (| (Go InC) |)
>         "infer"    -> (| Infer bigInTm |)
>         "jump"     -> (| Jump (| N variableParse |) |)
>         "lambda"   -> (| Lambda ident |)
>         "last"     -> (| (Go Last) |)
>         "make"     -> (| Make ident (%keyword ":"%) (| ~Nothing :<: bigInTm |)
>                        | Make ident (%keyword ":="%) maybeAscriptionParse
>                        |)
>         "module"   -> (| ModuleC ident |)
>         "next"     -> (| (Go Next) |)
>         "out"      -> (| (Go OutC) |)
>         "pi"       -> (| PiBoy ident (%keyword ":"%) bigInTm |)
>         "prev"     -> (| (Go Prev) |)
>         "root"     -> (| (Go RootC) |)
>         "quit"     -> (| Quit |)
>         "select"   -> (| Select (| N variableParse |) |)
>         "show"     -> (| Show bigInTm |)
>         "top"      -> (| (Go Top) |)
>         "ungawa"   -> (| Ungawa |)
>         "up"       -> (| (Go Up) |)
>         _          -> empty

> pFileName :: Parsley Token String
> pFileName = ident

> evalCommand :: Command INTM -> ProofState String
> evalCommand Apply           = apply             >> return "Applied."
> evalCommand Auncles         = infoAuncles
> evalCommand DoneC           = done              >> return "Done."
> evalCommand Dump            = infoDump
> evalCommand (Elaborate tm)  = infoElaborate tm
> evalCommand (Give tm)       = elabGive tm       >> return "Thank you."
> evalCommand (Go InC)        = goIn              >> return "Going in..."
> evalCommand (Go OutC)       = goOut             >> return "Going out..."
> evalCommand (Go Up)         = goUp              >> return "Going up..."
> evalCommand (Go Down)       = goDown            >> return "Going down..."
> evalCommand (Go Top)        = many goUp         >> return "Going to top..."
> evalCommand (Go Bottom)     = many goDown       >> return "Going to bottom..."
> evalCommand (Go Prev)       = prevGoal          >> return "Searching for previous goal..."
> evalCommand (Go RootC)      = many goOut        >> return "Going to root..."
> evalCommand (Go Next)       = nextGoal          >> return "Searching for next goal..."
> evalCommand (Go First)      = some prevGoal     >> return "Searching for first goal..."
> evalCommand (Go Last)       = some nextGoal     >> return "Searching for last goal..."
> evalCommand (Infer tm)      = infoInfer tm      
> evalCommand (Jump (N (P (n := _)))) = do
>     much goOut
>     goTo n
>     return ("Going to " ++ showName n ++ "...")
> evalCommand (Lambda x)      = lambdaBoy x       >> return "Made lambda boy!"
> evalCommand (Make x (mtm :<: ty)) = do
>     elabMake (x :<: ty)
>     goIn
>     case mtm of
>         Nothing  -> return "Appended goal!"
>         Just tm  -> elabGive tm >> return "Yessir."
> evalCommand (ModuleC s)     = makeModule s      >> return "Made module."
> evalCommand (PiBoy x ty)    = elabPiBoy (x :<: ty)  >> return "Made pi boy!"
> evalCommand (Select x)      = select x          >> return "Selected."
> evalCommand (Show x)        = return (show x)
> evalCommand Ungawa          = ungawa            >> return "Ungawa!"

> doCommand :: Command InTmRN -> ProofState String
> doCommand c = do
>     aus <- getAuncles
>     c' <- traverse (resolve aus) c
>               `catchMaybe` "doCommand: could not resolve names in command."
>     evalCommand c'

> doCommands :: [Command InTmRN] -> ProofState [String]
> doCommands cs = sequenceA (map doCommand cs)

> doCommandsAt :: [(Name, [Command InTmRN])] -> ProofState ()
> doCommandsAt [] = return ()
> doCommandsAt ((_, []):ncs) = doCommandsAt ncs
> doCommandsAt ((n, cs):ncs) = much goOut >> goTo n >> doCommands cs >> doCommandsAt ncs

> showPrompt :: Bwd Layer -> String
> showPrompt (_ :< l)  = showName (motherName (mother l)) ++ " > "
> showPrompt B0        = "> "

> printChanges :: ProofContext -> ProofContext -> IO ()
> printChanges from to = do
>     let Right as = evalStateT getAuncles from
>         Right bs = evalStateT getAuncles to
>     let (lost, gained)  = diff (as <>> F0) (bs <>> F0)
>     if lost /= F0
>         then putStrLn ("Left scope: " ++ showEntriesAbs (fmap reverseEntry (NF (fmap Right lost))) )
>         else return ()
>     if gained /= F0
>        then putStrLn ("Entered scope: " ++ showEntriesAbs (fmap reverseEntry (NF (fmap Right gained))))
>        else return ()

> diff :: (Eq a, Show a) => Fwd a -> Fwd a -> (Fwd a, Fwd a)
> diff (x :> xs) (y :> ys)
>     | x == y     = diff xs ys
>     | otherwise  = (x :> xs, y :> ys)
> diff xs ys = (xs, ys)
