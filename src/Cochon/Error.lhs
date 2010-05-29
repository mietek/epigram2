\section{Cochon error prettier}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.Error where

> import Control.Monad.Error
> import Text.PrettyPrint.HughesPJ

> import Evidences.Tm hiding (In)

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Distiller
> import DisplayLang.PrettyPrint

> import ProofState.ProofState
> import ProofState.ProofKit

%endif


\subsection{Catching the gremlins before they leave |ProofState|}


> catchUnprettyErrors :: StackError DInTmRN -> ProofState a
> catchUnprettyErrors e = do
>                   e' <- distillErrors e
>                   throwError e'

> distillErrors :: StackError DInTmRN -> ProofState (StackError DInTmRN)
> distillErrors e = sequence $ fmap (sequence . fmap distillError) e

> distillError :: ErrorTok DInTmRN -> ProofState (ErrorTok DInTmRN)
> distillError (TypedVal (v :<: t)) = do
>   vTm <- bquoteHere v
>   vDTm :=>: _ <- distillHere (t :>: vTm)
>   return $ UntypedTm vDTm
> distillError (UntypedVal v) = do
>   v'  <- bquoteHere v
>   tm  <- liftErrorState (moonshine v')
>   return $ UntypedTm tm
> distillError (UntypedINTM v') = do
>   tm  <- liftErrorState (moonshine v')
>   return $ UntypedTm tm   
> distillError e = return e



\subsection{Pretty-printing the stack trace}


> prettyStackError :: StackError DInTmRN -> Doc
> prettyStackError e = 
>     vcat $
>     fmap (text "Error:" <+>) $
>     fmap hsep $
>     fmap -- on the stack
>     (fmap -- on the token
>      prettyErrorTok) e


> prettyErrorTok :: ErrorTok DInTmRN -> Doc
> prettyErrorTok (StrMsg s) = text s
> prettyErrorTok (TypedTm (v :<: t)) = pretty v maxBound
> prettyErrorTok (UntypedTm t) = pretty t maxBound
> prettyErrorTok (TypedCan (v :<: t)) = pretty v maxBound
> prettyErrorTok (UntypedCan c) = pretty c maxBound
> prettyErrorTok (UntypedElim e) = pretty e maxBound

The following cases should be avoided as much as possible:

> prettyErrorTok (TypedVal (v :<: t)) = brackets $ text "typedV" <> (brackets $ text $ show v)
> prettyErrorTok (UntypedVal v) = brackets $ text "untypedV" <> (brackets $ text $ show v)
> prettyErrorTok (ERef (name := _)) = hcat $ punctuate  (char '.') 
>                                                       (map (\(x,n) ->  text x <> 
>                                                                        char '_' <> 
>                                                                        int n) name) 
> prettyErrorTok (UntypedINTM t) = brackets $ text "untypedT" <> (brackets $ text $ show t)

