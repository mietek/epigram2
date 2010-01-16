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

To parse a development, we represent it as a list of |DevLine|s, each
of which corresponds to a |Boy| or |Girl| entry and stores enough
information to reconstruct it. Note that at this stage, we simply tag
each girl with a list of commands to execute later.

> data DevLine
>   =  DLBoy BoyKind String InDTmRN
>   |  DLGirl String [DevLine] (Maybe InDTmRN :<: InDTmRN) [CTData]
>   |  DLModule String [DevLine] [CTData]

A module may have a list of girls in square brackets, followed by an optional
semicolon-separated list of commands.

> parseDevelopment :: Parsley Token [DevLine]
> parseDevelopment = bracket Square (many (pGirl <|> pModule)) 
>                 <|> pure []

\subsubsection{Parsing Girls}

A girl is an identifier, followed by a list of children, a definition
(which may be @?@), and optionally a list of commands:

> pGirl :: Parsley Token DevLine
> pGirl = (| DLGirl (|fst namePartParse|) -- identifier
>                   pLines                -- childrens (optional)
>                   pDefn                 -- definition
>                   pCTSuffix             -- commands (optional)
>                   (%keyword KwSemi%) 
>          |)

\paragraph{Parsing children:}

Children, if any, are enclosed inside square brackets. They can be of
several types: girl and module, that we have already defined, or
boy. Boy are defined below. The absence of children is signaled by the
@:=@ symbol.

> pLines :: Parsley Token [DevLine]
> pLines =  bracket Square (many (pGirl <|> pBoy <|> pModule)) 
>       <|> (keyword KwDefn *> pure [])

\paragraph{Parsing definitions:}

A definition is either a question mark or a term, ascripted by a
type. The question mark corresponds to an open goal. On the other
hand, giving a term corresponds to explicitly solving the goal.

> pDefn :: Parsley Token (Maybe InDTmRN :<: InDTmRN)
> pDefn =  (| (%keyword KwQ%) (%keyword KwAsc%) ~Nothing :<: pInDTm 
>           | id pAsc
>           |)
>   where pAsc = do
>         tm ::? ty <- pAscription
>         return $ Just tm :<: ty

\paragraph{Parsing commands:}

Commands can be typed directly in the developments by enclosing them
inside @[| ... |]@ brackets. They are parsed in one go by
|pCochonTactics|, so this is quite fragile. This is better used when
we know things work.

> pCTSuffix :: Parsley Token [CTData]
> pCTSuffix = bracket (SquareB "") pCochonTactics 
>          <|> pure []


\subsubsection{Parsing Modules}

A module is similar, but has no definition.

> pModule :: Parsley Token DevLine
> pModule = (| DLModule (|fst namePartParse|) -- identifier
>                       pLines                -- childrens (optional)
>                       pCTSuffix             -- commands (optional)
>                       (%keyword KwSemi%) 
>            |)

\subsubsection{Parsing Boys}

A boy is a $\lambda$-abstraction (represented by @\ x : T ->@) or a
$\Pi$-abstraction (represented by @(x : S) ->@).

> pBoy :: Parsley Token DevLine
> pBoy =  (| (%keyword KwLambda%)          -- \
>            (DLBoy LAMB)              
>            (| fst namePartParse |)       -- x
>            (%keyword KwAsc%)             -- :
>            (sizedInDTm (pred ArrSize))   -- T
>            (%keyword KwArr%) |)          -- ->
>         <|> 
>             (bracket Round               -- (
>              (| (DLBoy PIB)              
>                 (| fst namePartParse |)  -- x
>                 (%keyword KwAsc%)        -- :
>                 pInDTm |)) <*            -- S)
>                 keyword KwArr            -- ->


\subsection{Construction}

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

\subsection{Loading the files}

Once we have parsed a list of |DevLine|s, we need to construct a |Dev| from them.
The idea is to use commands defined in Section~\ref{sec:proofStateMonad} to build
up the proof state. 

> devLoad :: String -> IO (Bwd ProofContext)
> devLoad file = do
>   -- Load the development file
>   let devFile = dropExtension file ++ ".dev" 
>   dev <- withFile devFile ReadMode loadDevelopment
>          `catchError` \ _ -> return []
>   -- Load the development in an empty proof state
>   case runStateT (makeDev dev []) emptyContext of
>     Left errs -> do
>       putStrLn $ unlines $ "Failed to load development:" : errs
>       exitFailure
>     Right (ncs, loc) -> do
>       -- Load the commands file
>       commands <- withFile file ReadMode readCommands
>       -- Play them in the development
>       doCTacticsAt (([], commands) : ncs) (B0 :< loc)

The following companion function takes care of the dirty details: 
\begin{itemize}
\item Loading the content of the file;
\item Tokenizing the file
\item Parsing the development
\end{itemize}

> loadDevelopment :: Handle -> IO [DevLine]
> loadDevelopment file = do
>     f <- hGetContents file
>     -- Tokenize the development file
>     case parse tokenize f of
>       Left err -> do
>         putStrLn $ "loadDevelopment: failed to tokenize:\n" ++ 
>                    show err
>         exitFailure
>       Right toks ->
>           -- Parse the development
>           case parse parseDevelopment toks of
>             Left err -> do
>               putStrLn $ "loadDevelopment: failed to parse:\n" ++
>                            show err
>               exitFailure
>             Right dev -> do
>               -- Return the result
>               return dev
