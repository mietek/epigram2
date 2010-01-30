\section{Cochon (Command-line Interface)}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.Cochon where

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Error
> import Data.Foldable hiding (find)
> import Data.List
> import Data.Traversable hiding (sequence)
> import System.Exit
> import System.IO 

> import Kit.BwdFwd
> import Kit.Parsley
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import Evidences.Tm hiding (In)

> import DisplayLang.Lexer
> import DisplayLang.Naming
> import DisplayLang.TmParse
> import DisplayLang.Elaborator
> import DisplayLang.DisplayTm

> import ProofState.Developments
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import Tactics.Elimination
> import Tactics.Induction
> import Tactics.PropSimp

> import Cochon.DisplayCommands

> import Compiler.Compiler

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

> data CochonArg = StrArg String 
>                | InArg InDTmRN 
>                | ExArg ExDTmRN
>                | Optional CochonArg
>                | NoCochonArg


> argToStr :: CochonArg -> String
> argToStr (StrArg s) = s

> argToIn :: CochonArg -> InDTmRN
> argToIn (InArg a) = a

> argToEx :: CochonArg -> ExDTmRN
> argToEx (ExArg a) = a

> argOption :: (CochonArg -> a) -> CochonArg -> Maybe a
> argOption p (Optional x) = Just $ p x
> argOption _ NoCochonArg = Nothing


> parseExTm :: Parsley Token CochonArg
> parseExTm = (| ExArg pExDTm |)

> parseAscription :: Parsley Token CochonArg
> parseAscription = (| ExArg pAscriptionTC |)

> parseInTm :: Parsley Token CochonArg
> parseInTm = (| InArg pInDTm |)

> parseName :: Parsley Token CochonArg
> parseName = (| (ExArg . DP) nameParse |)

> parseString :: Parsley Token CochonArg
> parseString = (| StrArg ident |)

> parseOption :: Parsley Token CochonArg -> Parsley Token CochonArg
> parseOption p = (| Optional (bracket Square p) 
>                  | NoCochonArg |)


A Cochon tactic consinsts of:
\begin{description}
\item[|ctName|] the name of this tactic
\item[|ctParse|] a parser that parses the arguments for this tactic
\item[|ctIO|] an IO action to perform for a given list of arguments and current context
\item[|ctHelp|] the help text for this tactic
\end{description}

> data CochonTactic =
>     CochonTactic  {  ctName   :: String
>                   ,  ctParse  :: Parsley Token (Bwd CochonArg)
>                   ,  ctIO     :: [CochonArg] -> Bwd ProofContext -> IO (Bwd ProofContext)
>                   ,  ctHelp   :: String
>                   }

> instance Show CochonTactic where
>     show = ctName

> instance Eq CochonTactic where
>     ct1 == ct2  =  ctName ct1 == ctName ct2

> instance Ord CochonTactic where
>     compare ct1 ct2 = compare (ctName ct1) (ctName ct2)



We have some shortcuts for building common kinds of tactics:
|simpleCT| builds a tactic that works in the proof state,
and there are various specialised versions of it for nullary and
unary tactics.


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

> simpleCT :: String -> Parsley Token (Bwd CochonArg)
>     -> ([CochonArg] -> ProofState String) -> String -> CochonTactic
> simpleCT name parser eval help = CochonTactic
>     {  ctName = name
>     ,  ctParse = parser
>     ,  ctIO = (\as -> simpleOutput (eval as))
>     ,  ctHelp = help
>     } 

> nullaryCT :: String -> ProofState String -> String -> CochonTactic
> nullaryCT name eval help = simpleCT name (pure B0) (const eval) help

> unaryExCT :: String -> (ExDTmRN -> ProofState String) -> String -> CochonTactic
> unaryExCT name eval help = simpleCT
>     name
>     (| (B0 :<) parseExTm
>      | (B0 :<) parseAscription |)
>     (eval . argToEx . head)
>     help

> unaryInCT :: String -> (InDTmRN -> ProofState String) -> String -> CochonTactic
> unaryInCT name eval help = simpleCT
>     name
>     (| (B0 :<) parseInTm |)
>     (eval . argToIn . head)
>     help

> unDP (DP ref) = ref

> unaryNameCT :: String -> (RelName -> ProofState String) -> String -> CochonTactic
> unaryNameCT name eval help = simpleCT
>     name
>     (| (B0 :<) parseName |)
>     (eval . unDP . argToEx . head)
>     help
>   where unDP (DP ref) = ref

> unaryStringCT :: String -> (String -> ProofState String) -> String -> CochonTactic
> unaryStringCT name eval help = simpleCT
>     name
>     (| (B0 :<) parseString |)
>     (eval . argToStr . head)
>     help

The master list of Cochon tactics.

> cochonTactics :: [CochonTactic]
> cochonTactics = sort (

Construction tactics:


>     nullaryCT "apply" (apply >> return "Applied.")
>       "apply - applies the last entry in the development to a new subgoal."
>   : nullaryCT "done" (done >> return "Done.")
>       "done - solves the goal with the last entry in the development."
>   : unaryInCT "give" (\tm -> elabGiveNext tm >> return "Thank you.")
>       "give <term> - solves the goal with <term>."
>   : simpleCT 
>         "lambda"
>          (| (|(B0 :<) parseString (%keyword KwAsc%)|) :< parseInTm 
>           | (B0 :<) parseString |)
>          (\ args -> case args of
>              [StrArg s] -> lambdaBoy s >> return "Made lambda boy!"
>              [StrArg s, InArg ty] -> 
>                elabLamBoy (s :<: ty) >> return "Made lambda boy!")
>          ("lambda <x> - introduces a hypothesis.\n"++
>           "lambda <x> : <type> - introduces a new module parameter or hyp.")

>   : simpleCT
>         "make"
>         (| (|(B0 :<) parseString (%keyword KwAsc%)|) :< parseInTm
>          | (|(B0 :<) parseString (%keyword KwDefn%) |) <>< 
>              (| (\ (tm :<: ty) -> InArg tm :> InArg ty :> F0) pAscription |)
>          |)
>         (\ (StrArg s:tyOrTm) -> case tyOrTm of
>             [InArg ty] -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 return "Appended goal!"
>             [InArg tm, InArg ty] -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 elabGive tm
>                 return "Made."
>         )
>        ("make <x> : <type> - creates a new goal of the given type.\n"
>            ++ "make <x> := <term> - adds a definition to the context.")

>   : unaryStringCT "module" (\s -> makeModule s >> goIn >> return "Made module.")
>       "module <x> - creates a module with name <x>."

>   : simpleCT
>         "pi"
>          (| (|(B0 :<) parseString (%keyword KwAsc%)|) :< parseInTm |)
>         (\ [StrArg s, InArg ty] -> elabPiBoy (s :<: ty) >> return "Made pi boy!")
>         "pi <x> : <type> - introduces a pi boy."

>   : simpleCT
>       "program"
>       (|bwdList (pSep (keyword KwComma) parseString)|)
>       (\ as -> elabProgram (map argToStr as) >> return "Programming.")
>       "program <labels>: set up a programming problem."

>   : unaryNameCT "select" (\ x -> resolveHere x >>= select . N . P >> return "Selected.")
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

>   : unaryNameCT "jump" (\ x -> do
>       much goOut
>       (n := _) <- resolveHere x
>       goTo n
>       return ("Jumping to " ++ showName n ++ "...")
>     )
>       "jump <name> - moves to the definition of <name>."


Information tactics:

>   : unaryExCT "elaborate" infoElaborate
>       "elaborate <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."
>   : unaryExCT "infer" infoInfer
>       "infer <term> - elaborates <term> and infers its type."

>   : unaryInCT "parse" (return . show)
>       "parse <term> - parses <term> and displays the internal display-sytnax representation."

>   : unaryStringCT "show" (\s -> case s of
>         "auncles"  -> infoAuncles
>         "context"  -> infoContext 
>         "dump"     -> infoDump
>         "hyps"     -> infoHypotheses
>         "state"    -> prettyProofState
>         _          -> return "show: please specify exactly what to show."
>       )
>       "show <auncles/context/dump/hyps/state> - displays useless information."

>   : unaryExCT "whatis" infoWhatIs
>       "whatis <term> - prints the various representations of <term>."


Miscellaneous tactics:

>   : CochonTactic
>         {  ctName = "compile"
>         ,  ctParse = (|(|(B0 :<) parseName|) :< parseString|)
>         ,  ctIO = (\ [ExArg (DP r), StrArg fn] (locs :< loc) -> do
>             let  Right aus = evalStateT getAuncles loc
>                  Right dev = evalStateT getDev loc
>                  Right (n := _) = evalStateT (resolveHere r) loc
>             compileCommand n (reverseDev' dev) fn
>             putStrLn "Compiled."
>             return (locs :< loc)
>           )
>         ,  ctHelp = "compile <name> <file> - compiles the proof state with <name> as the main term to be evalauted, producing a binary called <file>."
>         }

>     : CochonTactic
>         {  ctName = "help"
>         ,  ctParse = (| (B0 :<) parseString
>                       | B0
>                       |)
>         ,  ctIO = (\ as locs -> do
>             case as of
>                 [] -> putStrLn ("Tactics available: " ++ tacticNames cochonTactics)
>                 [StrArg s] -> case tacticsMatching s of
>                     [] -> putStrLn "There is no tactic by that name."
>                     cts -> putStrLn (unlines (map ctHelp cts))
>             return locs
>           )
>         ,  ctHelp = "help - displays a list of supported tactics.\n"
>                       ++ "help <tactic> - displays help about <tactic>.\n\n"
>                       ++ "What, you expected 'help help' to produce an amusing response?"
>         }

>     : CochonTactic
>         {  ctName = "quit"
>         ,  ctParse = pure B0
>         ,  ctIO = (\ _ _ -> exitSuccess)
>         ,  ctHelp = "quit - terminates the program."
>         }

>     : CochonTactic
>         {  ctName = "save"
>         ,  ctParse = (| (B0 :<) parseString |)
>         ,  ctIO = (\ [StrArg fn] (locs :< loc) -> do
>             let Right s = evalStateT (much goOut >> prettyProofState) loc
>             writeFile fn s
>             putStrLn "Saved."
>             return (locs :< loc)
>           )
>         ,  ctHelp = "save <file> - saves proof state to the given file."
>         }
>             

>     : CochonTactic 
>         {  ctName = "undo"
>         ,  ctParse = pure B0
>         ,  ctIO = (\ _ (locs :< loc) -> case locs of
>             B0  -> putStrLn "Cannot undo."  >> return (locs :< loc) 
>             _   -> putStrLn "Undone."       >> return locs
>          )
>         ,  ctHelp = "undo - goes back to a previous state."
>         }

>     : CochonTactic 
>         {  ctName = "load"
>         ,  ctParse = (| (B0 :<) parseString |)
>         ,  ctIO = (\ [StrArg file] locs -> do
>                    commands <- withFile file ReadMode readCommands
>                                `catchError` \_ -> do
>                                  putStrLn $ "File " ++ file ++ " does not exist. Ignored."
>                                  return []
>                    doCTactics commands locs)
>         ,  ctHelp = "load <f> - load the commands stored in <f>"
>         }

Import more tactics from an aspect:

>     import <- CochonTactics
>     : [] )


> pFileName :: Parsley Token String
> pFileName = ident

The |tacticsMatching| function identifies Cochon tactics that match the
given string, either exactly or as a prefix.

> tacticsMatching :: String -> [CochonTactic]
> tacticsMatching x = case find ((x ==) . ctName) cochonTactics of
>     Just ct  -> [ct]
>     Nothing  -> filter (isPrefixOf x . ctName) cochonTactics

> tacticNames :: [CochonTactic] -> String
> tacticNames = intercalate ", " . map ctName


> type CTData = (CochonTactic, [CochonArg])

> readCommands :: Handle -> IO [CTData]
> readCommands file = do
>   f <- hGetContents file
>   case parse tokenizeCommands f of
>     Left err -> do
>       putStrLn $ "readCommands: failed to tokenize:\n" ++
>                  show err
>       exitFailure
>     Right lines -> do
>          t <- sequence $ map readCommand lines
>          return $ Data.List.concat t

> readCommand :: String -> IO [CTData]
> readCommand command =
>     case parse tokenize command of
>       Left err -> do
>         putStrLn $ "readCommand: failed to tokenize:\n" ++
>                    show err
>         exitFailure
>       Right toks -> do
>         case parse pCochonTactics toks of
>           Left err -> do
>             putStrLn $ "readCommand: failed to parse:\n" ++
>                        show err
>             exitFailure
>           Right command -> do
>             return command

                           


> tokenizeCommands :: Parsley Char [String]
> tokenizeCommands = (|id ~ [] (% pEndOfStream %)
>                     |id (% oneLineComment %) 
>                         (% consumeUntil' endOfLine %)
>                         tokenizeCommands
>                     |id (% openBlockComment %) 
>                         (% consumeUntil' closeBlockComment %) 
>                         tokenizeCommands
>                     |consumeUntil' endOfCommand : 
>                      tokenizeCommands
>                     |)
>     where endOfCommand = tokenEq ';' *> spaces *> endOfLine
>                      <|> pEndOfStream *> pure ()
>           endOfLine = tokenEq (head "\n") <|> pEndOfStream 
>           oneLineComment = tokenEq '-' *> tokenEq '-' 
>           openBlockComment = tokenEq '{' *> tokenEq '-'
>           closeBlockComment = tokenEq '-' *> tokenEq '}'
>           spaces = many $ tokenEq ' '



> pCochonTactic :: Parsley Token CTData
> pCochonTactic  = do
>     x <- ident
>     case tacticsMatching x of
>         [ct] -> do
>             args <- ctParse ct
>             return (ct, trail args)
>         [] -> fail "unknown tactic name."
>         cts -> fail ("ambiguous tactic name (could be " ++ tacticNames cts ++ ").")

> pCochonTactics :: Parsley Token [CTData]
> pCochonTactics = pSepTerminate (keyword KwSemi) pCochonTactic


> doCTactic :: CTData -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTactic (ct, args) (locs :< loc) = ctIO ct args (locs :< loc)

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
