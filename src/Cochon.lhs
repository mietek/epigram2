\section{Cochon (Command-line Interface)}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon where

> import Compiler
> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable hiding (find)
> import Data.List
> import Data.Traversable
> import System.Exit
> import System.IO (hFlush, stdout)

> import BwdFwd
> import Developments
> import DisplayCommands
> import DisplayTm
> import Distiller
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
> import Elimination

%endif

Here we have a very basic command-driven interface to the proof state monad.

> cochon :: ProofContext -> IO ()
> cochon loc = cochon' (B0 :< loc)

> cochon' :: Bwd ProofContext -> IO ()
> cochon' (locs :< loc@(ls, dev)) = do
>     showGoal loc

>     case evalStateT validateHere loc of
>         Left ss -> do
>             putStrLn "*** Warning: definition failed to type-check! ***"
>             putStrLn (unlines ss)
>         _ -> return ()

>     putStr (showPrompt ls)
>     hFlush stdout
>     l <- getLine
>     case parse tokenize l of 
>         Left pf -> do
>             putStrLn ("Tokenize failure: " ++ describePFailure pf id)
>             cochon' (locs :< loc)
>         Right ts ->
>           case parse pCochonTactics ts of
>               Left pf -> do
>                   putStrLn ("Parse failure: " ++ describePFailure pf (intercalate " " . map crushToken))
>                   cochon' (locs :< loc)
>               Right cds -> do
>                   locs' <- doCTactics cds (locs :< loc)
>                   cochon' locs'

> describePFailure :: PFailure a -> ([a] -> String) -> String
> describePFailure (PFailure (ts, fail)) f = (case fail of
>     Abort        -> "parser aborted."
>     EndOfStream  -> "end of stream."
>     EndOfParser  -> "end of parser."
>     Expect t     -> "expected " ++ f [t] ++ "."
>     Fail s       -> s
>   ) ++ (if length ts > 0
>        then ("\nSuccessfully parsed: ``" ++ f ts ++ "''.")
>        else "")


Because Cochon tactics can take different types of arguments,
we need a tagging mechanism to distinguish them, together
with projection functions.

> data CochonArg x = StrArg String | InArg (InDTm x) | ExArg (ExDTm x)
>     deriving (Functor, Foldable, Traversable)


> argToStr :: CochonArg x -> String
> argToStr (StrArg s) = s

> argToIn :: CochonArg x -> InDTm x
> argToIn (InArg a) = a

> argToEx :: CochonArg x -> ExDTm x
> argToEx (ExArg a) = a


A Cochon tactic consinsts of:
\begin{description}
\item[|ctName|] the name of this tactic
\item[|ctParse|] a parser that parses the arguments for this tactic
\item[|ctIO|] an IO action to perform for a given list of arguments and current context
\item[|ctHelp|] the help text for this tactic
\end{description}

> data CochonTactic =
>     CochonTactic  {  ctName   :: String
>                   ,  ctParse  :: Parsley Token [CochonArg RelName]
>                   ,  ctIO     :: [CochonArg REF] -> Bwd ProofContext -> IO (Bwd ProofContext)
>                   ,  ctHelp   :: String
>                   }

> instance Show CochonTactic where
>     show = ctName

> instance Eq CochonTactic where
>     ct1 == ct2  =  ctName ct1 == ctName ct2


We have some shortcuts for building common kinds of tactics:
|simpleCT| builds a tactic that works in the proof state,
and there are various specialised versions of it for nullary and
unary tactics.

> sing x = [x]

> simpleOutput :: ProofState String -> Bwd ProofContext -> IO (Bwd ProofContext)
> simpleOutput eval (locs :< loc) = do
>     case runStateT eval loc of
>         Right (s, loc') -> do
>             putStrLn s
>             return (locs :< loc :< loc')
>         Left ss -> do
>             putStrLn (unlines ("I'm sorry, Dave. I'm afraid I can't do that.":ss))
>             return (locs :< loc)
>             

> simpleCT :: String -> Parsley Token [CochonArg RelName]
>     -> ([CochonArg REF] -> ProofState String) -> String -> CochonTactic
> simpleCT name parser eval help = CochonTactic
>     {  ctName = name
>     ,  ctParse = parser
>     ,  ctIO = (\as -> simpleOutput (eval as))
>     ,  ctHelp = help
>     } 

> nullaryCT :: String -> ProofState String -> String -> CochonTactic
> nullaryCT name eval help = simpleCT name (pure []) (const eval) help

> unaryExCT :: String -> (EXDTM -> ProofState String) -> String -> CochonTactic
> unaryExCT name eval help = simpleCT
>     name
>     (| (sing . ExArg) pExDTm |)
>     (eval . argToEx . head)
>     help

> unaryInCT :: String -> (INDTM -> ProofState String) -> String -> CochonTactic
> unaryInCT name eval help = simpleCT
>     name
>     (| (sing . InArg) pInDTm |)
>     (eval . argToIn . head)
>     help

> unaryNameCT :: String -> (REF -> ProofState String) -> String -> CochonTactic
> unaryNameCT name eval help = simpleCT
>     name
>     (| (sing . ExArg . DP) nameParse |)
>     (eval . unDP . argToEx . head)
>     help
>   where unDP (DP ref) = ref

> unaryStringCT :: String -> (String -> ProofState String) -> String -> CochonTactic
> unaryStringCT name eval help = simpleCT
>     name
>     (| (sing . StrArg) ident |)
>     (eval . argToStr . head)
>     help

The master list of Cochon tactics.

> cochonTactics :: [CochonTactic]
> cochonTactics = 

Construction tactics:

>     nullaryCT "apply" (apply >> return "Applied.")
>       "apply - applies the last entry in the development to a new subgoal."
>   : nullaryCT "done" (done >> return "Done.")
>       "done - solves the goal with the last entry in the development."
>   : unaryInCT "give" (\tm -> elabGiveNext tm >> return "Thank you.")
>       "give <term> - solves the goal with <term>."
>   : unaryStringCT "lambda" (\s -> lambdaBoy s >> return "Made lambda boy!")
>       "lambda <x> - introduces a new hypothesis <x>."

>   : simpleCT
>         "make"
>         (| (| StrArg ident (%keyword ":"%) |) : (| (sing . InArg) pInDTm |)
>          | (| StrArg ident (%keyword ":="%) |) : (| (sing . ExArg) pAscription |)
>          |)
>         (\ [StrArg s, tyOrTm] -> case tyOrTm of
>             InArg ty -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 return "Appended goal!"
>             ExArg (tm ::? ty) -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 elabGive tm
>                 return "Made."
>         )
>        ("make <x> : <type> - creates a new goal of the given type.\n"
>            ++ "make <x> := <term> - adds a definition to the context.")

>   : unaryStringCT "module" (\s -> makeModule s >> return "Made module.")
>       "module <x> - creates a module with name <x>."

>   : simpleCT
>         "pi"
>          (| (| StrArg ident (%keyword ":"%) |) : (| (sing . InArg) pInDTm |) |)
>         (\ [StrArg s, InArg ty] -> elabPiBoy (s :<: ty) >> return "Made pi boy!")
>         "pi <x> : <type> - introduces a pi boy."

>   : simpleCT
>       "program"
>       (pSep (keyword ",") (| StrArg ident |))
>       (\ as -> elabProgram (map argToStr as) >> return "Programming.")
>       "program <labels>: set up a programming problem."

>   : unaryNameCT "select" (\r -> select (N (P r)) >> return "Selected.")
>       "select <name> - defines a copy of <name> in the current development."
>   : nullaryCT "ungawa" (ungawa >> return "Ungawa!")
>       "ungawa - tries to solve the current goal in a stupid way."


Navigation tactics:

>   : nullaryCT "in" (goIn >> return "Going in...")
>       "in - moves to the bottom-most development within the current one."
>   : nullaryCT "out" (goOut >> return "Going out...")
>       "out - moves to the development containing the current one."
>   : nullaryCT "up" (goUp >> return "Going up...")
>       "up - moves to the development above the current one."
>   : nullaryCT "down" (goDown >> return "Going down...")
>       "down - moves to the development below the current one."
>   : nullaryCT "top" (many goUp >> return "Going to top...")
>       "top - moves to the top-most development at the current level."
>   : nullaryCT "bottom" (many goDown >> return "Going to bottom...")
>       "bottom - moves to the bottom-most development at the current level."
>   : nullaryCT "previous" (prevGoal >> return "Going to previous goal...")
>       "previous - searches for the previous goal in the proof state."
>   : nullaryCT "root" (many goOut >> return "Going to root...")
>       "root - moves to the root of the proof state."
>   : nullaryCT "next" ( nextGoal >> return "Going to next goal...")
>       "next - searches for the next goal in the proof state."
>   : nullaryCT "first"  (some prevGoal >> return "Going to first goal...")
>       "first - searches for the first goal in the proof state."
>   : nullaryCT "last"   (some nextGoal >> return "Going to last goal...")
>       "last - searches for the last goal in the proof state."

>   : unaryNameCT "jump" (\(n := _) -> much goOut >> goTo n >> return ("Jumping to " ++ showName n ++ "..."))
>       "jump <name> - moves to the definition of <name>."


Information tactics:

>   : unaryExCT "elaborate" infoElaborate
>       "elaborate <term> - elaborates, evaluates, quotes and distills <term>."
>   : unaryExCT "infer" infoInfer
>       "infer <term> - elaborates <term> and infers its type."

>   : unaryStringCT "show" (\s -> case s of
>         "auncles" -> infoAuncles
>         "context" -> infoContext 
>         "dump" -> infoDump
>         "hyps" -> infoHypotheses
>         "state" -> prettyProofState 
>       )
>       "show <auncles/context/dump/hyps/state> - displays useless information."

> --evalCommand (Show (Term x))    = return (show x)


Miscellaneous tactics:

>   : CochonTactic
>         {  ctName = "compile"
>         ,  ctParse = (| (| (ExArg . DP) nameParse |) : (| (sing . StrArg) pFileName |) |)
>         ,  ctIO = (\ [ExArg (DP r), StrArg fn] (locs :< loc) -> do
>             let  Right aus = evalStateT getAuncles loc
>                  Right dev = evalStateT getDev loc
>             compileCommand (refName r) (reverseDev' dev) fn
>             putStrLn "Compiled."
>             return (locs :< loc)
>           )
>         ,  ctHelp = "compile <name> <file> - compiles the proof state with <name> as the main term to be evalauted, producing a binary called <file>."
>         }

>     : CochonTactic
>         {  ctName = "help"
>         ,  ctParse = (| (sing . StrArg) ident
>                       | []
>                       |)
>         ,  ctIO = (\ as locs -> do
>             case as of
>                 [] -> putStrLn ("Tactics available: " ++ tacticNames cochonTactics)
>                 [StrArg s] -> case tacticsMatching s of
>                     [ct] -> putStrLn (ctHelp ct)
>                     [] -> putStrLn "There is no tactic by that name."
>                     cts -> putStrLn ("Tactics matching: " ++ tacticNames cts)
>             return locs
>           )
>         ,  ctHelp = "help - displays a list of supported tactics.\n"
>                       ++ "help <tactic> - displays help about <tactic>.\n\n"
>                       ++ "What, you expected 'help help' to produce an amusing response?"
>         }

>     : CochonTactic
>         {  ctName = "quit"
>         ,  ctParse = pure []
>         ,  ctIO = (\ _ _ -> exitSuccess)
>         ,  ctHelp = "quit - terminates the program."
>         }

>     : CochonTactic 
>         {  ctName = "undo"
>         ,  ctParse = pure []
>         ,  ctIO = (\ _ (locs :< loc) -> case locs of
>             B0  -> putStrLn "Cannot undo."  >> return (locs :< loc) 
>             _   -> putStrLn "Undone."       >> return locs
>          )
>         ,  ctHelp = "undo - goes back to a previous state."
>         }


Import more tactics from an aspect:

>     import <- CochonTactics
>     : []

> pFileName :: Parsley Token String
> pFileName = ident

The |tacticsMatching| function identifies Cochon tactics that match the
given string, either exactly or as a prefix.

> tacticsMatching :: String -> [CochonTactic]
> tacticsMatching x = case find ((x ==) . ctName) cochonTactics of
>     Just ct  -> [ct]
>     Nothing  -> filter (isPrefixOf x . ctName) cochonTactics

> tacticNames :: [CochonTactic] -> String
> tacticNames = intercalate ", " . sort . map ctName


> type CTData = (CochonTactic, [CochonArg RelName])

> pCochonTactic :: Parsley Token CTData
> pCochonTactic  = do
>     x <- ident
>     case tacticsMatching x of
>         [ct] -> do
>             args <- ctParse ct
>             return (ct, args)
>         [] -> fail "unknown tactic name."
>         cts -> fail ("ambiguous tactic name (could be " ++ tacticNames cts ++ ").")

> pCochonTactics :: Parsley Token [CTData]
> pCochonTactics = pSepTerminate (keyword ";") pCochonTactic


> resolveArgs :: [CochonArg RelName] -> ProofState [CochonArg REF]
> resolveArgs args = do
>     aus <- getAuncles
>     args' <- resolveArgs' aus args 
>               `catchEither` "doCTactic: could not resolve names in command."
>     return args' 
>  where
>    resolveArgs' :: Entries -> [CochonArg RelName] -> Either [String] [CochonArg REF]
>    resolveArgs' aus (StrArg s : args) = (| ~(StrArg s) : (resolveArgs' aus args) |)
>    resolveArgs' aus (InArg tm : args) = (| (|InArg (resolve aus tm) |) : (resolveArgs' aus args) |)
>    resolveArgs' aus (ExArg tm : args) = (| (|ExArg (resolveEx aus tm) |) : (resolveArgs' aus args) |)
>    resolveArgs' aus [] = pure []

> doCTactic :: CTData -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTactic (ct, args) (locs :< loc) = do
>     case evalStateT (resolveArgs args) loc of
>         Right args' -> do
>             locs' <- ctIO ct args' (locs :< loc)
> --                    printChanges loc loc'
>             return locs'
>         Left ss -> do
>             putStrLn (unlines ("I'm sorry, Dave. I'm afraid I can't do that.":ss))
>             return (locs :< loc) 

> doCTactics :: [CTData] -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTactics [] locs = return locs
> doCTactics (cd:cds) locs = do
>     locs' <- doCTactic cd locs
>     doCTactics cds locs'

> doCTacticsAt :: [(Name, [CTData])] -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTacticsAt [] locs = return locs
> doCTacticsAt ((_, []):ncs) locs = doCTacticsAt ncs locs
> doCTacticsAt ((n, cs):ncs) (locs :< loc) = do
>     let Right loc' = execStateT (much goOut >> goTo n) loc
>     locs' <- doCTactics cs (locs :< loc :< loc')
>     doCTacticsAt ncs locs'




> showGoal :: ProofContext -> IO ()
> showGoal loc = case evalStateT getHoleGoal loc of
>     Right (_ :=>: ty) ->
>         let Right s = evalStateT (bquoteHere ty >>= prettyHere . (SET :>:)) loc
>         in putStrLn ("Goal: " ++ show s)
>     Left _ -> return ()

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
