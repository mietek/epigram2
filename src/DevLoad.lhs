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
> import Root
> import Rules
> import Tm
> import TmParse

%endif


\subsection{Parsing}

To parse a development, we represent it as a list of |DevLine|s, each of
which corresponds to a |Boy| or |Girl| entry and stores enough information
to reconstruct it. Note that at this stage, we simply tag each girl with
a list of commands to execute later.

> data DevLine
>   =  DLBoy BoyKind String InTmRN
>   |  DLGirl String [DevLine] (Maybe InTmRN :<: InTmRN) [Command InTmRN]
>      deriving Show

A module may have a list of girls in square brackets, followed by an optional
semicolon-separated list of commands.

> pModule :: Parsley Token ([DevLine], [Command InTmRN])
> pModule = (| pTopDevLines, (pSep (keyword ";") pCommand) |)
>   where
>     pTopDevLines :: Parsley Token [DevLine]
>     pTopDevLines =  bracket Square (many pGirl) <|> pure []

A girl is an identifier, followed by a list of children (or the \verb!:=! symbol if
there are none), a definition (which may be \verb!?!), and optionally a list of commands
in \verb![| |]! brackets.

> pGirl :: Parsley Token DevLine
> pGirl = (| DLGirl (|fst namePartParse|) pLines pDefn pCommandSuffix (%keyword ";"%) |)
>   where
>     pLines :: Parsley Token [DevLine]
>     pLines =  bracket Square (many (pGirl <|> pBoy)) <|> (keyword ":=" *> pure [])
>
>     pDefn :: Parsley Token (Maybe InTmRN :<: InTmRN)
>     pDefn =  (| (%keyword "?"%) (%keyword ":"%) ~Nothing :<: bigInTm 
>               | id maybeAscriptionParse
>               |)
>
>     pCommandSuffix :: Parsley Token [Command InTmRN]
>     pCommandSuffix = bracket (SquareB "") (pSep (keyword ";") pCommand) <|> pure []

A boy is a $\lambda$-abstraction (represented by \verb!\ x : T ->!) or a $\Pi$-abstraction
(represented by \verb!(x : S) ->!). 

> pBoy :: Parsley Token DevLine
> pBoy =  (| (%keyword "\\"%) (DLBoy LAMB) (| fst namePartParse |) (%keyword ":"%) littleInTm (%keyword "->"%) |)
>         <|> (bracket Round (| (DLBoy PIB) (| fst namePartParse |) (%keyword ":"%) littleInTm |)) <* keyword "->"


\subsection{Construction}

Once we have parsed a list of |DevLine|s, we need to construct a |Dev| from them.
The idea is to use commands defined in Section~\ref{sec:proofStateMonad} to build
up the proof state. The |devLoad| function takes care of this process.

> devLoad :: [Token] -> ProofState ()
> devLoad ts = case parse pModule ts of
>   Left pf -> throwError' $ "Failed to parse development: " ++ show pf
>   Right (dls, cs) -> do
>     ncs <- makeDev dls []
>     doCommandsAt ncs
>     doCommands cs
>     much goOut

The |makeDev| function updates the proof state to represent the given list of |DevLine|s,
accumulating pairs of names and command lists along the way.

> makeDev :: [DevLine] -> [(Name, [Command InTmRN])] -> ProofState [(Name, [Command InTmRN])]
> makeDev []      ncs = return ncs
> makeDev (l:ls)  ncs = makeEntry l ncs >>= makeDev ls

> makeEntry :: DevLine -> [(Name, [Command InTmRN])] -> ProofState [(Name, [Command InTmRN])]
> makeEntry (DLGirl x kids (mtipTm :<: tipTys) commands) ncs = do
>     n <- withRoot (flip name x)
>     let ref = n := HOLE :<: (error "makeEntry: ref undefined")
>     root <- getDevRoot
>     putDevEntry (E ref (last n) (Girl LETG (B0, error "makeEntry: tip undefined", room root x))
>                     (error "makeEntry: type undefined"))
>     putDevRoot (roos root)
>     goIn
>     ncs' <- makeDev kids ncs     
>     tipTy <- resolveHere tipTys 
>     aus <- getGreatAuncles
>     kids' <- getDevEntries
>     let goalTy = liftType aus (inferGoalType kids' tipTy)
>     goOutSilently
>     Just (E _ _ (Girl LETG (es, _, root')) _) <- removeDevEntry
>     putDevEntry (E (n := HOLE :<: evTm goalTy) (last n) 
>                    (Girl LETG (es, Unknown (tipTy :=>: evTm tipTy), root')) goalTy)
>     case mtipTm of
>         Nothing -> return ()
>         Just tm -> goIn >> resolveHere tm >>= giveSilently
>     case commands of
>         []  -> return ncs'
>         _   -> return ((n, commands):ncs')

> makeEntry (DLBoy LAMB x tys) ncs = do
>     ty <- resolveHere tys
>     Just () <- withRoot (check (SET :>: ty))     
>     root <- getDevRoot
>     Root.freshRef (x :<: evTm ty)
>         (\ref r -> do 
>            putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>            putDevRoot r
>          ) root
>     return ncs

> makeEntry (DLBoy PIB x tys) ncs = do 
>     ty <- resolveHere tys
>     Just () <- withRoot (check (SET :>: ty))
>     root <- getDevRoot
>     Root.freshRef (x :<: evTm ty)
>         (\ref r -> do
>            putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>            putDevRoot r
>          ) root
>     return ncs