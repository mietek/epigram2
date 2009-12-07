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
>               | id maybeAscriptionParse
>               |)
>
>     pCommandSuffix :: Parsley Token [Command InTmRN]
>     pCommandSuffix = bracket (SquareB "") (pSep (keyword ";") pCommand) <|> pure []

> pBoy :: Parsley Token DevLine
> pBoy =  (| (%keyword "\\"%) (DLBoy LAMB) ident (%keyword ":"%) bigInTm (%keyword "->"%) |)
>         <|> (bracket Round (| (DLBoy PIB) ident (%keyword ":"%) bigInTm |)) <* keyword "->"


> makeDev :: [DevLine] -> ProofState ()
> makeDev [] = return ()
> makeDev (l:ls) = makeEntry l >> makeDev ls

> makeEntry :: DevLine -> ProofState ()
> makeEntry (DLGirl x kids (mtipTm :<: tipTys) commands) = do
>     n <- withRoot (flip name x)
>     let ref = n := HOLE :<: undefined
>     root <- getDevRoot
>     putDevEntry (E ref (last n) (Girl LETG (B0, undefined, room root x)) undefined)
>     putDevRoot (roos root)
>     goIn
>     makeDev kids     
>     tipTy <- resolveHere tipTys 
>     kids' <- getDevEntries
>     let goalTy = inferGoalType tipTy kids'
>     goOut
>     Just (E _ _ (Girl LETG (es, _, root')) _) <- removeDevEntry
>     putDevEntry (E (n := HOLE :<: evTm goalTy) (last n) (Girl LETG (es, Unknown (tipTy :=>: evTm tipTy), root')) goalTy)
>     
>     case mtipTm of
>         Nothing -> return ()
>         Just tm -> goIn >> resolveHere tm >>= give

> makeEntry (DLBoy LAMB x tys) = do
>     ty <- resolveHere tys
>     Just () <- withRoot (check (SET :>: ty))     
>     root <- getDevRoot
>     Root.freshRef (x :<: evTm ty)
>         (\ref r -> do 
>            putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>            putDevRoot r
>          ) root

> makeEntry (DLBoy PIB x tys) = do 
>     ty <- resolveHere tys
>     Just () <- withRoot (check (SET :>: ty))
>     root <- getDevRoot
>     Root.freshRef (x :<: evTm ty)
>         (\ref r -> do
>            putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>            putDevRoot r
>          ) root


> inferGoalType :: INTM -> Bwd Entry -> INTM
> inferGoalType ty B0 = ty
> inferGoalType ty (es' :< E _ _ (Girl _ _) _)      = inferGoalType ty es'
> inferGoalType ty (es' :< E _ (x,_) (Boy LAMB) s)  = inferGoalType (PI s (L (x :. ty))) es'
> inferGoalType ty (es' :< E _ (x,_) (Boy PIB) s)   = inferGoalType SET es'

> devLoad :: [Token] -> ProofState ()
> devLoad ts = case parse pModule ts of
>   Left _ -> lift Nothing
>   Right (dls, cs) -> makeDev dls >> doCommands cs >> much goOut