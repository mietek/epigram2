\section{Loading Developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module DevLoad (devLoad) where

> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.Writer
> import Control.Monad.State
> import Control.Monad.Instances
> import Control.Applicative
> import Data.Char
> import Data.Maybe
> import Data.Foldable hiding (elem)
> import Data.Traversable

> import BwdFwd
> import Cochon
> import Developments
> import Elaborator
> import Lexer
> import MissingLibrary
> import Naming
> import Parsley
> import ProofState
> import Root
> import Rules
> import Tm
> import TmParse
> import Rooty

%endif


\subsection{Parsing}

To parse a development, we represent it as a list of |DevLine|s, each of
which corresponds to a |Boy| or |Girl| entry and stores enough information
to reconstruct it. Note that at this stage, we simply tag each girl with
a list of commands to execute later.

> data DevLine
>   =  DLBoy BoyKind String InDTmRN
>   |  DLGirl String [DevLine] (Maybe InDTmRN :<: InDTmRN) [Command InDTmRN]
>   |  DLModule String [DevLine] [Command InDTmRN]
>      deriving Show

A module may have a list of girls in square brackets, followed by an optional
semicolon-separated list of commands.

> pRootModule :: Parsley Token ([DevLine], [Command InDTmRN])
> pRootModule = (| pTopDevLines, (pSep (keyword ";") pCommand) |)
>   where
>     pTopDevLines :: Parsley Token [DevLine]
>     pTopDevLines =  bracket Square (many (pGirl <|> pModule)) <|> pure []

A girl is an identifier, followed by a list of children (or the \verb!:=! symbol if
there are none), a definition (which may be \verb!?!), and optionally a list of commands
in \verb![| |]! brackets.

> pGirl :: Parsley Token DevLine
> pGirl = (| DLGirl (|fst namePartParse|) pLines pDefn pCommandSuffix (%keyword ";"%) |)

A module is similar, but has no definition.

> pModule :: Parsley Token DevLine
> pModule = (| DLModule (|fst namePartParse|) pLines pCommandSuffix (%keyword ";"%) |)


> pLines :: Parsley Token [DevLine]
> pLines =  bracket Square (many (pGirl <|> pBoy <|> pModule)) <|> (keyword ":=" *> pure [])
>
> pDefn :: Parsley Token (Maybe InDTmRN :<: InDTmRN)
> pDefn =  (| (%keyword "?"%) (%keyword ":"%) ~Nothing :<: pInDTm 
>               | id maybeAscriptionParse
>               |)
>
> pCommandSuffix :: Parsley Token [Command InDTmRN]
> pCommandSuffix = bracket (SquareB "") (pSep (keyword ";") pCommand) <|> pure []

A boy is a $\lambda$-abstraction (represented by \verb!\ x : T ->!) or a $\Pi$-abstraction
(represented by \verb!(x : S) ->!). 

> pBoy :: Parsley Token DevLine
> pBoy =  (| (%keyword "\\"%) (DLBoy LAMB) (| fst namePartParse |) (%keyword ":"%)
>                (sizedInDTm (pred ArrSize)) (%keyword "->"%) |)
>         <|> (bracket Round (| (DLBoy PIB) (| fst namePartParse |) (%keyword ":"%) pInDTm |)) <* keyword "->"


\subsection{Construction}

Once we have parsed a list of |DevLine|s, we need to construct a |Dev| from them.
The idea is to use commands defined in Section~\ref{sec:proofStateMonad} to build
up the proof state. The |devLoad| function takes care of this process.

> devLoad :: [Token] -> ProofState ()
> devLoad ts = case parse pRootModule ts of
>   Left pf -> throwError' $ "Failed to parse development: " ++ show pf
>   Right (dls, cs) -> do
>     ncs <- makeDev dls []
>     doCommandsAt ncs
>     doCommands cs
>     much goOut

The |makeDev| function updates the proof state to represent the given list of |DevLine|s,
accumulating pairs of names and command lists along the way.

> makeDev :: [DevLine] -> [(Name, [Command InDTmRN])] -> ProofState [(Name, [Command InDTmRN])]
> makeDev []      ncs = return ncs
> makeDev (l:ls)  ncs = makeEntry l ncs >>= makeDev ls

> makeEntry :: DevLine -> [(Name, [Command InDTmRN])] -> ProofState [(Name, [Command InDTmRN])]
> makeEntry (DLGirl x kids (mtipTm :<: tipTys) commands) ncs = do
>     n <- makeModule x
>     goIn
>     ncs' <- makeDev kids ncs     
>     tipTyd <- resolveHere tipTys
>     tipTy :=>: tipTyv <- elaborate False (SET :>: tipTyd) -- FIXME: This needs some thought
>     kids' <- getDevEntries
>     moduleToGoal (tipTy :=>: tipTyv)
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
>     Root.freshRef (x :<: evTm ty)
>         (\ref r -> do 
>            putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>            putDevRoot r
>          ) root
>     return ncs

> makeEntry (DLBoy PIB x tys) ncs = do 
>     tyd <- resolveHere tys
>     ty :=>: tyv <- elaborate False (SET :>: tyd)
>     root <- getDevRoot
>     Root.freshRef (x :<: evTm ty)
>         (\ref r -> do
>            putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>            putDevRoot r
>          ) root
>     return ncs
