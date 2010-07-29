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
> import DisplayLang.PrettyPrint

> import ProofState.Edition.ProofState
> import ProofState.Interface.ProofKit

> import Distillation.Distiller
> import Distillation.Moonshine

%endif


\subsection{Catching the gremlins before they leave |ProofState|}


> catchUnprettyErrors :: StackError DInTmRN -> ProofState a
> catchUnprettyErrors e = do
>                   e' <- distillErrors e
>                   throwError e'

> distillErrors :: StackError DInTmRN -> ProofState (StackError DInTmRN)
> distillErrors e = sequence $ fmap (sequence . fmap distillError) e

> distillError :: ErrorTok DInTmRN -> ProofState (ErrorTok DInTmRN)
> distillError (ErrorVAL (v :<: mt)) = do
>     vTm   <- bquoteHere v
>     vDTm  <- case mt of
>         Just t   -> return . termOf =<< distillHere (t :>: vTm)
>         Nothing  -> liftErrorState DTIN (moonshine vTm)
>     return $ ErrorTm (vDTm :<: Nothing)
> distillError (ErrorTm (DTIN t :<: mt)) = do
>     d <- liftErrorState DTIN (moonshine t)
>     return $ ErrorTm (d :<: Nothing)
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
> prettyErrorTok (StrMsg s)              = text s
> prettyErrorTok (ErrorTm    (v :<: _))  = pretty v maxBound
> prettyErrorTok (ErrorCan   v)  = pretty v maxBound
> prettyErrorTok (ErrorElim  e)  = pretty e maxBound

The following cases should be avoided as much as possible:

> prettyErrorTok (ErrorREF (name := _))  = text $ showName name
> prettyErrorTok (ErrorVAL (v :<: _))    = text "ErrorVAL" <>
>                                              (brackets $ text $ show v)