\section{Loading Developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Cochon.DevLoad (devLoad) where

> import Control.Monad.State
> import Control.Monad.Error
> import Control.Applicative
> import System.Exit
> import System.IO
> import System.FilePath.Posix

> import Kit.BwdFwd
> import Kit.Parsley

> import Cochon.Cochon

> import ProofState.Developments

> import DisplayLang.DisplayTm
> import DisplayLang.Elaborator
> import DisplayLang.Lexer
> import DisplayLang.Naming
> import DisplayLang.TmParse

> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm

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
> parseDevelopment  = bracket Square (many (pGirl <|> pModule)) 
>                   <|> pure []

\subsubsection{Parsing Girls}

A girl is an identifier, followed by a list of children, a definition
(which may be @?@), and optionally a list of commands:

> pGirl :: Parsley Token DevLine
> pGirl =  (| DLGirl  ident                  -- identifier
>                     pLines                 -- childrens (optional)
>                     pDefn                  -- definition
>                     pCTSuffix              -- commands (optional)
>                     (%keyword KwSemi%) 
>          |)

\paragraph{Parsing children:}

Children, if any, are enclosed inside square brackets. They can be of
several types: girl and module, that we have already defined, or
boy. Boy are defined below. The absence of children is signaled by the
@:=@ symbol.

> pLines  :: Parsley Token [DevLine]
> pLines  =  bracket Square (many (pGirl <|> pBoy <|> pModule)) 
>         <|> (keyword KwDefn *> pure [])

\paragraph{Parsing definitions:}

A definition is either a question mark or a term, ascripted by a
type. The question mark corresponds to an open goal. On the other
hand, giving a term corresponds to explicitly solving the goal.

> pDefn :: Parsley Token (Maybe InDTmRN :<: InDTmRN)
> pDefn  =  (|  (%keyword KwQ%) (%keyword KwAsc%) ~Nothing :<: pInDTm 
>           |  id pAsc
>           |)
>   where pAsc = do
>          tm ::? ty <- pAscription
>          return $ Just tm :<: ty

\paragraph{Parsing commands:}

Commands can be typed directly in the developments by enclosing them
inside @[| ... |]@ brackets. They are parsed in one go by
|pCochonTactics|, so this is quite fragile. This is better used when
we know things work.

> pCTSuffix  :: Parsley Token [CTData]
> pCTSuffix  = bracket (SquareB "") pCochonTactics 
>            <|> pure []


\subsubsection{Parsing Modules}

A module is similar, but has no definition.

> pModule :: Parsley Token DevLine
> pModule =  (| DLModule  ident                  -- identifier
>                         pLines                 -- children (optional)
>                         pCTSuffix              -- commands (optional)
>                         (%keyword KwSemi%) 
>            |)

\subsubsection{Parsing Boys}

A boy is a $\lambda$-abstraction (represented by @\ x : T ->@) or a
$\Pi$-abstraction (represented by @(x : S) ->@).

> pBoy :: Parsley Token DevLine
> pBoy =  (|  (%keyword KwLambda%)          -- @\@
>             (DLBoy LAMB)              
>             ident                         -- @x@
>             (%keyword KwAsc%)             -- @:@
>             (sizedInDTm (pred ArrSize))   -- @T@
>             (%keyword KwArr%) |)          -- @->@
>         <|> 
>             (bracket Round                -- @(@
>              (|  (DLBoy PIB)              
>                  ident                    -- @x@
>                  (%keyword KwAsc%)        -- @:@
>                  pInDTm |)) <*            -- @S)@
>                  keyword KwArr            -- @->@


\subsection{Construction}

Once we have parsed a development as a list of |DevLine|, we interpret
it in the |ProofState| monad. This is the role of |makeDev|. It
updates the proof state to represent the given list of |DevLine|s,
accumulating pairs of names and command lists along the way.

> type NamedCommand = (Name, [CTData])
>
> makeDev :: [DevLine] -> [NamedCommand] -> ProofState [NamedCommand]
> makeDev []      ncs = return ncs
> makeDev (l:ls)  ncs = makeEntry l ncs >>= makeDev ls

Each line of development is processed by |makeEntry|. This is where
the magic happen and the |ProofState| is updated.

> makeEntry :: DevLine -> [NamedCommand] -> ProofState [NamedCommand]

\paragraph{Making a Girl:}

To make a girl, we operate in 4 steps. First of all, we jump in a
module in which we make our kids. Once this is done, we resolve our
display syntax goal into a term: we are therefore able to turn the
module in a girl. The third step consists in solving the problem if we
were provided a solution, or give up if not. Finally, we accumulate
the commands which might have been issued.

\question{Why is there a FIXME?}

> makeEntry (DLGirl x kids (mtipTm :<: tipTys) commands) ncs = do
>     -- Open a module named by her name
>     n <- makeModule x
>     goIn
>     -- Recursively build the kids
>     ncs' <- makeDev kids ncs
>     -- Translate |tipTys| into a real |INTM|
>     tipTyd <- resolveHere tipTys
>     -- FIXME: This needs some thought:
>     tipTy :=>: tipTyv <- elaborate False (SET :>: tipTyd)
>     -- Turn the module into a Girl of |tipTy|
>     moduleToGoal tipTy
>     -- Were we provided a solution?
>     case mtipTm of
>         Nothing -> do -- No.
>                    -- Leave
>                    goOut
>         Just tms -> do -- Yes!
>             -- Translate the solution |tms| to an |INTM|
>             -- And give it
>             tmd <- resolveHere tms
>             elabGive tmd
>             return ()
>     -- Is there any tactics to be executed?
>     case commands of
>         []  -> do -- No.
>                -- Return the kids' commands
>                return ncs'
>         _   -> do -- Yes!
>                -- Accumulate our commands 
>                -- With the ones from the kids
>                return $ (n, commands) : ncs'

\paragraph{Making a Module:}

Making a module involves much less effort than to make a girl. This is
indeed a stripped-down version of the above code for girls. 

> makeEntry (DLModule x kids commands) ncs = do
>     -- Make the module
>     n <- makeModule x
>     goIn
>     -- Recursively build the kids
>     ncs' <- makeDev kids ncs
>     -- Leave
>     goOut
>     -- Is there any tactics to be executed?
>     case commands of
>         []  -> do -- No.
>                -- Return the kids' commands
>                return ncs'
>         _   -> do -- Yes!
>                -- Accumulate our commands 
>                -- With the ones from the kids
>                return $ (n, commands) : ncs'

\paragraph{Making a Boy:}

To make a boy, be him Lambda or Pi, is straightforward. First, we need
to translate the type in display syntax to an |INTM|. Then, we make a
fresh reference of that type. Finally, we store that reference in the
development. 

Note that we have to be careful when manipulating the |NameSupply|:
better be sure that we maintain a coherent state of our name supply.

> makeEntry (DLBoy LAMB x tys) ncs = do
>     -- Translate the display |tys| into an |INTM|
>     tyd <- resolveHere tys
>     ty :=>: tyv <- elaborate False (SET :>: tyd)
>     -- Make a fresh reference of that type
>     nsupply <- getDevNSupply
>     freshRef (x :<: tyv)
>         (\ref r -> do 
>            -- Register |ref| as a Lambda boy
>            putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>            -- Save the updated |NameSupply|!
>            putDevNSupply r
>          ) nsupply
>     -- Pass the accumulated commands
>     return ncs
>
> makeEntry (DLBoy PIB x tys) ncs = do 
>     -- Translate the display |tys| into an |INTM|
>     tyd <- resolveHere tys
>     ty :=>: tyv <- elaborate False (SET :>: tyd)
>     -- Make a fresh reference of that type
>     nsupply <- getDevNSupply
>     freshRef (x :<: tyv)
>         (\ref r -> do
>            -- Register |ref| as a Pi boy
>            putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>            -- Save the updated |NameSupply|!
>            putDevNSupply r
>          ) nsupply
>     -- Pass the accumulated commands
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
