\section{Elaboration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module Elaborator where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import BwdFwd
> import Developments
> import Naming
> import PrettyPrint
> import ProofState
> import Root
> import Rooty
> import Rules
> import Tm
> import MissingLibrary

%endif

\subsection{Elaborator}

> subgoal :: (TY :>: String) -> ProofState (INTM :=>: VAL)
> subgoal (ty :>: x) = do
>     ty' <- bquoteHere ty
>     g <- make (x :<: ty')
>     return (g :=>: evTm g)

> elaborate :: (TY :>: INDTM) -> ProofState (INTM :=>: VAL)
> elaborate (C ty :>: C tm) = do
>     v <- canTy elaborate (ty :>: tm)
>     return $ (C $ fmap (\(x :=>: _) -> x) v) :=>: (C $ fmap (\(_ :=>: x) -> x) v)

> elaborate (ty :>: Q x) = subgoal (ty :>: x)

> elaborate (PI s t :>: L sc) = do
>   r <- getDevRoot
>   (tm :=>: tv) <- Root.freshRef ("x" :<: s) (\ref r ->
>       elaborate (t $$ A (pval ref) :>: underScope sc ref)) r
>   case sc of
>       K _  -> return (L (K tm) :=>: L (K tv))
>       _    -> return (L ("x" :. tm) :=>: L (H B0 "x" tm))
>   

> elaborate (w :>: N n) = do
>   (y :>: _) <- elabInfer n
>   eq <- withRoot (equal (SET :>: (w, y)))
>   guard eq `replaceError` ("elaborate: inferred type " ++ show y ++ " of " ++ show n
>                              ++ " is not " ++ show w)
>   return (N n :=>: evTm (N n))

> elaborate tt = throwError' ("elaborate: can't cope with " ++ show tt)


> elabInfer :: EXDTM -> ProofState (TY :>: EXTM)
> elabInfer (P x) = return (pty x :>: P x)

> elabInfer (t :$ s) = do
>     (C ty :>: t') <- elabInfer t
>     (s', ty') <- elimTy elaborate (evTm t' :<: ty) s
>     let s'' = fmap (\(x :=>: _) -> x) s'
>     return (ty' :>: (t' :$ s''))

> elabInfer (op :@ ts) = do
>   (vs, t) <- opTy op chev ts
>   let vs' = fmap (\((x :=>: _) :=>: _) -> x) vs
>   return (t :>: op :@ vs')
>       where chev (t :>: x) = do 
>               ch <- elaborate (t :>: x)
>               return $ ch :=>: evTm x

> elabInfer (t :? ty) = do
>   (ty' :=>: vty)  <- elaborate (SET :>: ty)
>   (t'  :=>: _)    <- elaborate (vty :>: t)
>   return (vty :>: t' :? ty')

> elabInfer tt = throwError' ("elabInfer: can't cope with " ++ show tt)


\subsection{Display-Term Commands}

\subsubsection{Information}

> infoElaborate :: INDTM -> ProofState INTM
> infoElaborate (N tm) = do
>     _ :>: tm' <- elabInfer tm
>     return (N tm')
> infoElaborate _ = throwError' "infoElaborate: can only elaborate neutral terms."

> infoInfer :: INDTM -> ProofState TY
> infoInfer (N tm) = do
>     ty :>: _ <- elabInfer tm
>     return ty
> infoInfer _ = throwError' "infoInfer: can only infer the type of neutral terms."


\subsubsection{Construction}

> elabGive :: INDTM -> ProofState ()
> elabGive (Q "") = return ()
> elabGive tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             (tm' :=>: tv) <- elaborate (tipTy :>: tm)
>             give tm'
>         _  -> throwError' "give: only possible for incomplete goals."


> elabMake :: (String :<: INDTM) -> ProofState INTM
> elabMake (s :<: ty) = do
>     tt <- elaborate (SET :>: ty)
>     make' (s :<: tt)


> elabPiBoy :: (String :<: INDTM) -> ProofState ()
> elabPiBoy (s :<: ty) = do
>     tt <- elaborate (SET :>: ty)
>     piBoy' (s :<: tt)
