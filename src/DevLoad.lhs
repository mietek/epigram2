\section{Loading Developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module DevLoad (devLoad) where

> import Control.Monad.State
> import Control.Applicative
> import Data.Char
> import Data.Maybe
> import Data.Foldable hiding (elem)
> import Data.Traversable
> import System.Exit
> import System.IO
> 

> import BwdFwd
> import Cochon
> import Developments
> import DisplayTm
> import Elaborator
> import Lexer
> import Naming
> import Parsley
> import ProofState
> import Root
> import Tm
> import TmParse
> import Rooty

%endif


\subsection{Parsing a Development}

To parse a development, we represent it as a list of |DevLine|s, each of
which corresponds to a |Boy| or |Girl| entry and stores enough information
to reconstruct it. Note that at this stage, we simply tag each girl with
a list of commands to execute later.

> data DevLine
>   =  DLBoy BoyKind String InDTmRN
>   |  DLGirl String [DevLine] (Maybe InDTmRN :<: InDTmRN) [CTData]
>   |  DLModule String [DevLine] [CTData]

A module may have a list of girls in square brackets, followed by an optional
semicolon-separated list of commands.

> parseDevelopment :: Parsley Token [DevLine]
> parseDevelopment = bracket Square (many (pGirl <|> pModule)) 
>                    <|> pure []

A girl is an identifier, followed by a list of children (or the \verb!:=! symbol if
there are none), a definition (which may be \verb!?!), and optionally a list of commands
in \verb![| |]! brackets.

> pGirl :: Parsley Token DevLine
> pGirl = (| DLGirl (|fst namePartParse|) pLines pDefn pCTSuffix (%keyword KwSemi%) |)

A module is similar, but has no definition.

> pModule :: Parsley Token DevLine
> pModule = (| DLModule (|fst namePartParse|) pLines pCTSuffix (%keyword KwSemi%) |)


> pLines :: Parsley Token [DevLine]
> pLines =  bracket Square (many (pGirl <|> pBoy <|> pModule)) <|> (keyword KwDefn *> pure [])
>
> pDefn :: Parsley Token (Maybe InDTmRN :<: InDTmRN)
> pDefn =  (| (%keyword KwQ%) (%keyword KwAsc%) ~Nothing :<: pInDTm 
>           | id pAsc
>           |)
>   where
>     pAsc = do
>         tm ::? ty <- pAscription
>         return (Just tm :<: ty)
>
> pCTSuffix :: Parsley Token [CTData]
> pCTSuffix = bracket (SquareB "") pCochonTactics <|> pure []

A boy is a $\lambda$-abstraction (represented by \verb!\ x : T ->!) or a $\Pi$-abstraction
(represented by \verb!(x : S) ->!). 

> pBoy :: Parsley Token DevLine
> pBoy =  (| (%keyword KwLambda%) (DLBoy LAMB) (| fst namePartParse |)
>                (%keyword KwAsc%) (sizedInDTm (pred ArrSize)) (%keyword KwArr%) |)
>         <|> (bracket Round (| (DLBoy PIB) (| fst namePartParse |)
>                (%keyword KwAsc%) pInDTm |)) <* keyword KwArr


\subsection{Construction}

Once we have parsed a list of |DevLine|s, we need to construct a |Dev| from them.
The idea is to use commands defined in Section~\ref{sec:proofStateMonad} to build
up the proof state. The |devLoad| function takes care of this process.

> devLoad :: String -> IO (Bwd ProofContext)
> devLoad file = do
>   let devFile = dropExtension file ++ ".dev" 
>   dev <- withFile devFile ReadMode loadDevelopment
>          `catchError` \ _ -> return []
>   case runStateT (makeDev dev []) emptyContext of
>     Left errs -> do
>       putStrLn $ unlines $ "Failed to load development:" : errs
>       exitFailure
>     Right (ncs, loc) -> do
>       commands <- withFile file ReadMode readCommands
>       doCTacticsAt (([], commands) : ncs) (B0 :< loc)


> loadDevelopment :: Handle -> IO [DevLine]
> loadDevelopment file = do
>     f <- hGetContents file
>     case parse tokenize f of
>       Left err -> do
>         putStrLn $ "loadDevelopment: failed to tokenize:\n" ++ 
>                    show err
>         exitFailure
>       Right toks ->
>           case parse parseDevelopment toks of
>             Left err -> do
>               putStrLn $ "loadDevelopment: failed to parse:\n" ++
>                            show err
>               exitFailure
>             Right dev -> do
>               return dev

> readCommands :: Handle -> IO [CTData]
> readCommands file = do
>   f <- hGetContents file
>   case parse tokenizeCommands f of
>     Left err -> do
>       putStrLn $ "readCommands: failed to tokenize:\n" ++
>                  show err
>       exitFailure
>     Right lines -> do
>          sequence $ map (\s -> putStrLn $ "[" ++ s ++ "]")lines
>          sequence $ map readCommand lines

> readCommand :: String -> IO CTData
> readCommand command =
>     case parse tokenize command of
>       Left err -> do
>         putStrLn $ "readCommand: failed to tokenize:\n" ++
>                    show err
>         exitFailure
>       Right toks -> do
>         case parse pCochonTactic toks of
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
>           endOfLine = tokenEq '\n' <|> pEndOfStream 
>           oneLineComment = tokenEq '-' *> tokenEq '-' 
>           openBlockComment = tokenEq '{' *> tokenEq '-'
>           closeBlockComment = tokenEq '-' *> tokenEq '}'
>           spaces = many $ tokenEq ' '




The |makeDev| function updates the proof state to represent the given list of |DevLine|s,
accumulating pairs of names and command lists along the way.

> makeDev :: [DevLine] -> [(Name, [CTData])] -> ProofState [(Name, [CTData])]
> makeDev []      ncs = return ncs
> makeDev (l:ls)  ncs = makeEntry l ncs >>= makeDev ls

> makeEntry :: DevLine -> [(Name, [CTData])] -> ProofState [(Name, [CTData])]
> makeEntry (DLGirl x kids (mtipTm :<: tipTys) commands) ncs = do
>     n <- makeModule x
>     goIn
>     ncs' <- makeDev kids ncs     
>     tipTyd <- resolveHere tipTys
>     tipTy :=>: tipTyv <- elaborate False (SET :>: tipTyd) -- FIXME: This needs some thought
>     kids' <- getDevEntries
>     moduleToGoal tipTy
>     case mtipTm of
>         Nothing -> goOut
>         Just tms -> do
>             tmd <- resolveHere tms
>             elabGive tmd
>             return ()
>     case commands of
>         []  -> return ncs'
>         _   -> return ((n, commands):ncs')

> makeEntry (DLModule x kids commands) ncs = do
>     n <- withRoot (flip name x)
>     root <- getDevRoot
>     putDevEntry (M n (B0, Module, room root x))
>     putDevRoot (roos root)
>     goIn
>     ncs' <- makeDev kids ncs     
>     goOut
>     case commands of
>         []  -> return ncs'
>         _   -> return ((n, commands):ncs')

> makeEntry (DLBoy LAMB x tys) ncs = do
>     tyd <- resolveHere tys
>     ty :=>: tyv <- elaborate False (SET :>: tyd)
>     root <- getDevRoot
>     freshRef (x :<: tyv)
>         (\ref r -> do 
>            putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>            putDevRoot r
>          ) root
>     return ncs

> makeEntry (DLBoy PIB x tys) ncs = do 
>     tyd <- resolveHere tys
>     ty :=>: tyv <- elaborate False (SET :>: tyd)
>     root <- getDevRoot
>     freshRef (x :<: tyv)
>         (\ref r -> do
>            putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>            putDevRoot r
>          ) root
>     return ncs
