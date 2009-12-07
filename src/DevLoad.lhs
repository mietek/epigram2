\section{Loading Developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module DevLoad (devLoad) where

> import Control.Monad
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

> data DevLine
>   =  DLBoy BoyKind String InTmRN
>   |  DLGirl String [DevLine] (Maybe InTmRN :<: InTmRN)
>          [Command InTmRN]
>      deriving Show


A module has many girls in square brackets, followed by a semicolon-separated
list of commands.

> pModule :: Parsley Token ([DevLine], [Command InTmRN])
> pModule = (| pTopDevLines, (pSep (keyword ";") pCommand) |)
>   where
>     pTopDevLines :: Parsley Token [DevLine]
>     pTopDevLines =  bracket Square (many pGirl) <|> pure []


> pGirl :: Parsley Token DevLine
> pGirl = (| DLGirl ident pLines pDefn pCommandSuffix (%keyword ";"%) |)
>   where
>     pLines :: Parsley Token [DevLine]
>     pLines =  bracket Square (many (pGirl <|> pBoy)) <|> (keyword ":=" *> pure [])
>
>     pDefn :: Parsley Token (Maybe InTmRN :<: InTmRN)
>     pDefn =  (| (%keyword "?"%) (%keyword ":"%) ~Nothing :<: bigInTm 
>               | id pAscription
>               |)
>
>     pAscription :: Parsley Token (Maybe InTmRN :<: InTmRN)
>     pAscription = do  tm :? ty <- ascriptionParse
>                       return (Just tm :<: ty)

>     pCommandSuffix :: Parsley Token [Command InTmRN]
>     pCommandSuffix = bracket (SquareB "") (pSep (keyword ";") pCommand) <|> pure []

> pBoy :: Parsley Token DevLine
> pBoy =  (| (%keyword "\\"%) (DLBoy LAMB) ident (%keyword ":"%) bigInTm (%keyword "->"%) |)
>         <|> (bracket Round (| (DLBoy PIB) ident (%keyword ":"%) bigInTm |)) <* keyword "->"


> makeDev :: [DevLine] -> ProofState ()
> makeDev [] = return ()
> makeDev (l:ls) = makeEntry l >> makeDev ls

> makeEntry :: DevLine -> ProofState ()
> makeEntry (DLGirl s kids (mtm :<: ty) commands) = do
>     ty' <- resolveHere ty
>     make (s :<: ty')
>     goIn
>     makeDev kids
>     case mtm of
>         Nothing -> goOut
>         Just tm -> resolveHere tm >>= give

> makeEntry (DLBoy LAMB s _) = lambdaBoy s

> makeEntry (DLBoy PIB s ty) = do
>     ty' <- resolveHere ty
>     piBoy (s :<: ty')

> devLoad :: [Token] -> ProofState ()
> devLoad ts = case parse pModule ts of
>   Left _ -> lift Nothing
>   Right (dls, cs) -> makeDev dls >> doCommands cs >> much goOut