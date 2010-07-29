\section{Record declaration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.Record where

> import Control.Applicative
> import Control.Monad.Identity

> import Data.Monoid hiding (All)
> import Data.Traversable

> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Rules
> import Evidences.Mangler

> import NameSupply.NameSupplier

> import ProofState.Structure.Developments
> import ProofState.Edition.ProofState
> import ProofState.Interface.ProofKit

> import Elaboration.Elaborator

> import DisplayLang.DisplayTm
> import DisplayLang.Name

%endif

> elabRecord ::  String -> [(String , DInTmRN)] -> ProofState (EXTM :=>: VAL)
> elabRecord name fields = undefined -- XXX: not yet implemented


> import -> CochonTactics where
>   : CochonTactic
>         {  ctName = "record"
>         ,  ctParse = do 
>              nom <- tokenString
>              keyword KwDefn
>              scs <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm)
>               (keyword KwSemi)
>              return $ B0 :< nom :< pars :< scs
>         , ctIO = (\ [StrArg nom, pars, cons] -> simpleOutput $ 
>                     elabRecord nom (argList (argPair argToStr argToIn) pars) 
>                                    (argList (argPair argToStr argToIn) cons) 
>                       >> return "Record'd.")
>         ,  ctHelp = "record <name> [<para>]* := [(<label> : <ty>) ;]* - builds a record type."
>         } 
