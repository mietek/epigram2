\section{Record declaration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.Record where

> import Evidences.Tm
> import Evidences.Mangler

> import ProofState.Edition.ProofState

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
