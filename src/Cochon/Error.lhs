\section{Cochon error prettier}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.Error where

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Error
> import Data.List
> import System.Exit
> import System.IO 
> import Text.PrettyPrint.HughesPJ


> import Kit.BwdFwd hiding ((<+>))
> import Kit.Parsley

> import NameSupply.NameSupply

> import Evidences.Tm hiding (In)

> import DisplayLang.Lexer
> import DisplayLang.Naming
> import DisplayLang.TmParse
> import DisplayLang.Elaborator
> import DisplayLang.DisplayTm
> import DisplayLang.PrettyPrint

> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import Tactics.Elimination
> import Tactics.Induction
> import Tactics.PropSimp
> import Tactics.Information

> import Cochon.CommandLexer

> import Compiler.Compiler

%endif

> prettyStackError :: StackError InDTmRN -> Doc
> prettyStackError e = 
>     vcat $
>     fmap (text "Error:" <+>) $
>     fmap hsep $
>     fmap -- on the stack
>     (fmap -- on the token
>      prettyErrorTok) e


> prettyErrorTok :: ErrorTok InDTmRN -> Doc
> prettyErrorTok (StrMsg s) = text s
> prettyErrorTok (TypedTm (v :<: t)) = pretty v maxBound
> prettyErrorTok (UntypedTm t) = pretty t maxBound
> prettyErrorTok (TypedCan (v :<: t)) = pretty v maxBound
> prettyErrorTok (UntypedCan c) = pretty c maxBound
> prettyErrorTok (UntypedElim e) = pretty e maxBound
> prettyErrorTok (TypedVal (v :<: t)) = brackets $ text "typedV" <> (brackets $ text $ show v)
> prettyErrorTok (UntypedVal v) = brackets $ text "untypedV" <> (brackets $ text $ show v)
> prettyErrorTok (ERef (name := _)) = hcat $ punctuate  (char '.') 
>                                                       (map (\(x,n) ->  text x <> 
>                                                                        char '_' <> 
>                                                                        int n) name) 
> prettyErrorTok (UntypedINTM t) = brackets $ text "untypedT" <> (brackets $ text $ show t)


> catchUnprettyErrors :: StackError InDTmRN -> ProofState a
> catchUnprettyErrors e = do
>                   e' <- distillErrors e
>                   throwError e'

> distillErrors :: StackError InDTmRN -> ProofState (StackError InDTmRN)
> distillErrors e = sequence $ fmap (sequence . fmap distillError) e

> distillError :: ErrorTok InDTmRN -> ProofState (ErrorTok InDTmRN)
> distillError (TypedVal (v :<: t)) = do
>   vTm <- bquoteHere v
>   vDTm :=>: _ <- distillHere (t :>: vTm)
>   return $ UntypedTm vDTm
> distillError e = return e
