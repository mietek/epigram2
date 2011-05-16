\section{Cochon error prettier}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Cochon.Error where

> import Control.Monad.Error
> import Text.PrettyPrint.HughesPJ

> import Evidences.Tm
> import Evidences.ErrorHandling

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import ProofState.Edition.ProofState
> import ProofState.Interface.ProofKit

> import Distillation.Distiller
> import Distillation.Moonshine

%endif


\subsection{Catching the gremlins before they leave |ProofState|}


> catchUnprettyErrors :: StackError -> ProofState a
> catchUnprettyErrors e = do
>                   e' <- distillErrors e
>                   throwError e'

> distillErrors :: StackError -> ProofState StackError 
> distillErrors e = sequence $ fmap (sequence . fmap distillError) e

> distillError :: ErrorTok -> ProofState ErrorTok 
> distillError e@(ErrorTm (Nothing :>: t)) = (do
>     d <- moonshine 0 t
>     return $ StrMsg (renderHouseStyle (pretty d AppSize))) 
>   `catchError` \_ -> return e
> distillError e@(ErrorTm (Just ty :>: t)) = (do
>     d <- distill (ev ty :>: ev t) 0
>     return $ StrMsg (renderHouseStyle (pretty d AppSize))) 
>   `catchError` \_ -> return e
> distillError e = return e


\subsection{Pretty-printing the stack trace}


> prettyStackError :: StackError -> Doc
> prettyStackError e = 
>     vcat $
>     fmap (text "Error:" <+>) $
>     fmap hsep $
>     fmap -- on the stack
>     (fmap -- on the token
>      prettyErrorTok) e


> prettyErrorTok :: ErrorTok -> Doc
> prettyErrorTok (StrMsg s)                  = text s
> prettyErrorTok (ErrorTm (Nothing :>: tm))  = text $ show tm
> prettyErrorTok (ErrorTm (Just ty :>: tm))  = text $ show tm ++ " : " ++ show ty
