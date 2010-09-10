\section{Cochon (Command-line Interface)}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.Cochon where

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Error
> import Data.Foldable
> import Data.Traversable
> import Data.List hiding (find)
> import System
> import System.Exit
> import System.IO 

> import NameSupply.NameSupply

> import Evidences.Tm hiding (In)

> import DisplayLang.Lexer
> import DisplayLang.Name
> import DisplayLang.TmParse
> import DisplayLang.DisplayTm
> import DisplayLang.PrettyPrint

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Module
> import ProofState.Interface.NameResolution
> import ProofState.Interface.Solving
> import ProofState.Interface.Parameter

> import Tactics.Elimination
> import Tactics.PropositionSimplify
> import Tactics.ProblemSimplify
> import Tactics.Information
> import Tactics.Gadgets
> import Tactics.Data
> import Tactics.IData
> import Tactics.Relabel
> import Tactics.ShowHaskell
> import Tactics.Matching
> import Tactics.Unification

> import Elaboration.Elaborator
> import Elaboration.Scheduler

> import Distillation.Distiller

> import Cochon.CommandLexer
> import Cochon.Error

> import Compiler.Compiler

> import Kit.BwdFwd
> import Kit.Parsley
> import Kit.MissingLibrary

%endif


Here we have a very basic command-driven interface to the proof state monad.

> cochon :: ProofContext -> IO ()
> cochon loc = cochon' (B0 :< loc)

> cochon' :: Bwd ProofContext -> IO ()
> cochon' (locs :< loc) = do
>     -- Safety belt: this *must* type-check!      
>     validateDevelopment (locs :< loc)
>     -- Show goal and prompt
>     putStr $ fst $ runProofState showPrompt loc
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


> paranoid = False
> veryParanoid = False

> validateDevelopment :: Bwd ProofContext -> IO ()
> validateDevelopment locs@(_ :< loc) = if veryParanoid
>     then Data.Foldable.mapM_ validateCtxt locs -- XXX: there must be a better way to do that
>     else if paranoid
>         then validateCtxt loc
>         else return ()
>   where validateCtxt loc = do
>             case evalStateT (validateHere `catchError` catchUnprettyErrors) loc of
>               Left ss -> do
>                          putStrLn "*** Warning: definition failed to type-check! ***"
>                          putStrLn $ renderHouseStyle $ prettyStackError ss
>               _ -> return ()


> showPrompt :: ProofState String
> showPrompt = do
>     mty <- optional getHoleGoal
>     case mty of
>         Just (_ :=>: ty)  -> (|(showGoal ty) ++ showInputLine|)
>         Nothing           -> showInputLine
>   where
>     showGoal :: TY -> ProofState String
>     showGoal ty@(LABEL _ _) = do
>         h <- infoHypotheses
>         s <- prettyHere . (SET :>:) =<< bquoteHere ty
>         return $ h ++ "\n" ++ "Programming: " ++ show s ++ "\n"
>     showGoal ty = do
>         s <- prettyHere . (SET :>:) =<< bquoteHere ty
>         return $ "Goal: " ++ show s ++ "\n"
>
>     showInputLine :: ProofState String
>     showInputLine = do
>         mn <- optional getCurrentName
>         case mn of
>             Just n   -> return $ showName n ++ " > "
>             Nothing  -> return "> "


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

           

The |tacticsMatching| function identifies Cochon tactics that match the
given string, either exactly or as a prefix.

> tacticsMatching :: String -> [CochonTactic]
> tacticsMatching x = case find ((x ==) . ctName) cochonTactics of
>     Just ct  -> [ct]
>     Nothing  -> filter (isPrefixOf x . ctName) cochonTactics

> tacticNames :: [CochonTactic] -> String
> tacticNames = intercalate ", " . map ctName


Given a proof state command and a context, we can run the command with
|runProofState| to produce a message (either the response from the command or
the error message) and |Maybe| a new proof context.

> runProofState :: ProofState String -> ProofContext
>     -> (String, Maybe ProofContext)
> runProofState m loc =
>     case runStateT (m `catchError` catchUnprettyErrors) loc of
>         Right (s, loc')  -> (s, Just loc')
>         Left ss          -> (renderHouseStyle $ prettyStackError ss, Nothing)



> simpleOutput :: ProofState String -> Bwd ProofContext -> IO (Bwd ProofContext)
> simpleOutput eval (locs :< loc) = do
>     case runProofState (eval <* startScheduler) loc of
>         (s, Just loc') -> do
>             putStrLn s
>             return (locs :< loc :< loc')
>         (s, Nothing) -> do
>             putStrLn "I'm sorry, Dave. I'm afraid I can't do that."
>             putStrLn s
>             return (locs :< loc)


We have some shortcuts for building common kinds of tactics:
|simpleCT| builds a tactic that works in the proof state,
and there are various specialised versions of it for nullary and
unary tactics.

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

> unaryExCT :: String -> (DExTmRN -> ProofState String) -> String -> CochonTactic
> unaryExCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenExTm
>      | (B0 :<) tokenAscription |)
>     (eval . argToEx . head)
>     help

> unaryInCT :: String -> (DInTmRN -> ProofState String) -> String -> CochonTactic
> unaryInCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenInTm |)
>     (eval . argToIn . head)
>     help

> unDP :: DExTm p x -> x
> unDP (DP ref ::$ []) = ref

> unaryNameCT :: String -> (RelName -> ProofState String) -> String -> CochonTactic
> unaryNameCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenName |)
>     (eval . unDP . argToEx . head)
>     help

> unaryStringCT :: String -> (String -> ProofState String) -> String -> CochonTactic
> unaryStringCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenString |)
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
>          (| (|bwdList (pSep (keyword KwComma) tokenString) (%keyword KwAsc%)|) :< tokenInTm 
>           | bwdList (pSep (keyword KwComma) tokenString)
>           |)
>          (\ args -> case args of
>             [] -> return "This lambda needs no introduction!"
>             _ -> case last args of
>               InArg ty  -> Data.Traversable.mapM (elabLamParam . (:<: ty) . argToStr) (init args)
>                                >> return "Made lambda!"
>               _         -> Data.Traversable.mapM (lambdaParam . argToStr) args
>                                >> return "Made lambda!"
>            )
>          ("lambda <labels> - introduces one or more hypotheses.\n"++
>           "lambda <labels> : <type> - introduces new module parameters or hypotheses.")

>   : simpleCT
>         "let"
>         (| (| (B0 :< ) tokenString |) :< tokenScheme |)
>         (\ [StrArg x, SchemeArg s] -> do
>             elabLet (x :<: s)
>             optional problemSimplify
>             optional seekGoal
>             return ("Let there be " ++ x ++ "."))
>         "let <label> <scheme> : <type> - set up a programming problem with a scheme."

>   : simpleCT
>         "make"
>         (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm
>          | (|(B0 :<) tokenString (%keyword KwDefn%) |) <>< 
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
>          (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm |)
>         (\ [StrArg s, InArg ty] -> elabPiParam (s :<: ty) >> return "Made pi!")
>         "pi <x> : <type> - introduces a pi."

>   : simpleCT
>       "program"
>       (|bwdList (pSep (keyword KwComma) tokenString)|)
>       (\ as -> elabProgram (map argToStr as) >> return "Programming.")
>       "program <labels>: set up a programming problem."

>   : nullaryCT "ungawa" (ungawa >> return "Ungawa!")
>       "ungawa - tries to solve the current goal in a stupid way."


Navigation tactics:

>   : nullaryCT "in" (goIn >> return "Going in...")
>       "in - moves to the bottom-most development within the current one."
>   : nullaryCT "out" (goOutBelow >> return "Going out...")
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
>       (n := _) <- resolveDiscard x
>       goTo n
>       return ("Jumping to " ++ showName n ++ "...")
>     )
>       "jump <name> - moves to the definition of <name>."


Miscellaneous tactics:

>   : CochonTactic
>         {  ctName = "execute"
>         ,  ctParse = (|(B0 :<) tokenString|)
>         ,  ctIO = (\ [StrArg fn] (locs :< loc) -> do
>             exit <- system fn
>             putStrLn $ if (exit == ExitSuccess) then "Success." else "Failure."
>             return (locs :< loc)
>           )
>         ,  ctHelp = "execute <command> - executes the given system command."
>         }

>     : CochonTactic
>         {  ctName = "help"
>         ,  ctParse = (| (B0 :<) tokenString
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
>         ,  ctParse = (| (B0 :<) tokenString |)
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

>     : nullaryCT "validate" (validateHere >> return "Validated.")
>         "validate - re-checks the definition at the current location."  

>     : CochonTactic 
>         {  ctName = "load"
>         ,  ctParse = (| (B0 :<) tokenString |)
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

> import <- CochonTacticsCode


> pFileName :: Parsley Token String
> pFileName = ident



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
>          t <- Data.Traversable.sequence $ map readCommand lines
>          return $ Data.List.concat t

> readCommand :: String -> IO [CTData]
> readCommand command =
>     case parse tokenize command of
>       Left err -> do
>         putStrLn $ "readCommand: failed to tokenize:\n" ++
>                    show err
>         putStrLn $ "Input was: " ++ command
>         exitFailure
>       Right toks -> do
>         case parse pCochonTactics toks of
>           Left err -> do
>             putStrLn $ "readCommand: failed to parse:\n" ++
>                        show err
>             putStrLn $ "Input was: " ++ command
>             exitFailure
>           Right command -> do
>             return command

                           


> tokenizeCommands :: Parsley Char [String]
> tokenizeCommands = (|id ~ [] (% pEndOfStream %)
>                     |id (% oneLineComment %) 
>                         (% consumeUntil' endOfLine %)
>                         tokenizeCommands
>                     |id (% openBlockComment %)
>                         (% (eatNestedComments 0) %)
>                         tokenizeCommands
>                     |id (spaces *> endOfLine *> tokenizeCommands)
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
>           eatNestedComments (-1) = (|id ~ ()|)
>           eatNestedComments i = (|id  (% openBlockComment %)
>                                       (eatNestedComments (i+1))
>                                  |id (% closeBlockComment %)
>                                      (eatNestedComments (i-1))
>                                  |id (% nextToken %)
>                                      (eatNestedComments i) |)


> pCochonTactic :: Parsley Token CTData
> pCochonTactic  = do
>     x <- (|id ident
>           |key anyKeyword
>           |)
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
>     let Right loc' = execStateT (goTo n) loc
>     locs' <- doCTactics cs (locs :< loc :< loc')
>     doCTacticsAt ncs locs'




> printChanges :: ProofContext -> ProofContext -> IO ()
> printChanges from to = do
>     let Right as = evalStateT getInScope from
>         Right bs = evalStateT getInScope to
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
