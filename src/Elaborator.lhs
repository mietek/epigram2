\section{Elaboration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, TypeOperators, TypeSynonymInstances #-}

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


> elaborate :: Bool -> (TY :>: INDTM) -> ProofState (INTM :=>: VAL)
> elaborate top (C ty :>: C tm) = do
>     v <- canTy (elaborate False) (ty :>: tm)
>     return $ (C $ fmap (\(x :=>: _) -> x) v) :=>: (C $ fmap (\(_ :=>: x) -> x) v)

> elaborate top (ty :>: Q x) = subgoal (ty :>: x)

> elaborate False (PI s (L (K t)) :>: L (K dtm)) = do
>     (tm :=>: tmv) <- elaborate False (t :>: dtm)
>     return (L (K tm) :=>: L (K tmv))

> elaborate False (PI s t :>: L sc) = do
>     let x :: String = case sc of { (x :. _) -> x ; K _ -> "_" }
>     pi' <- bquoteHere (PI s t)
>     make ("h" :<: pi')
>     goIn
>     l <- lambdaBoy x
>     h <- elabGive (underScope sc l)
>     return (h :=>: evTm h)

> elaborate True (PI s t :>: L sc) = do
>     let x :: String = case sc of { (x :. _) -> x ; K _ -> "_" }
>     l <- lambdaBoy x
>     elaborate True (t $$ A (pval l) :>: underScope sc l)
>     
    
> elaborate top (w :>: N n) = do
>   (y :>: _) <- elabInfer n
>   eq <- withRoot (equal (SET :>: (w, y)))
>   guard eq `replaceError` ("elaborate: inferred type " ++ show y ++ " of " ++ show n
>                              ++ " is not " ++ show w)
>   return (N n :=>: evTm (N n))

> elaborate top tt = throwError' ("elaborate: can't cope with " ++ show tt)


> elabInfer :: EXDTM -> ProofState (TY :>: EXTM)
> elabInfer (P x) = return (pty x :>: P x)

> elabInfer (t :$ s) = do
>     (C ty :>: t') <- elabInfer t
>     (s', ty') <- elimTy (elaborate False) (evTm t' :<: ty) s
>     let s'' = fmap (\(x :=>: _) -> x) s'
>     return (ty' :>: (t' :$ s''))

> elabInfer (op :@ ts) = do
>   (vs, t) <- opTy op chev ts
>   let vs' = fmap (\((x :=>: _) :=>: _) -> x) vs
>   return (t :>: op :@ vs')
>       where chev (t :>: x) = do 
>               ch <- elaborate False (t :>: x)
>               return $ ch :=>: evTm x

> elabInfer (t :? ty) = do
>   (ty' :=>: vty)  <- elaborate False (SET :>: ty)
>   (t'  :=>: _)    <- elaborate False (vty :>: t)
>   return (vty :>: t' :? ty')

> elabInfer tt = throwError' ("elabInfer: can't cope with " ++ show tt)


\subsection{Display-Term Commands}

\subsubsection{Information}

> infoElaborate :: INDTM -> ProofState INTM
> infoElaborate (N tm) = do
>     makeModule "elab"
>     goIn
>     _ :>: tm' <- elabInfer tm
>     tm <- bquoteHere (evTm (N tm'))
>     goOut
>     dropModule
>     return tm
> infoElaborate _ = throwError' "infoElaborate: can only elaborate neutral terms."

> infoInfer :: INDTM -> ProofState TY
> infoInfer (N tm) = do
>     makeModule "infer"
>     goIn
>     ty :>: _ <- elabInfer tm
>     goOut
>     dropModule
>     return ty
> infoInfer _ = throwError' "infoInfer: can only infer the type of neutral terms."


\subsubsection{Construction}

> elabGive :: INDTM -> ProofState INTM
> elabGive tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             case tm of
>                 Q "" -> do
>                     GirlMother ref _ _ <- getMother
>                     goOut
>                     return (N (P ref))
>                 _ -> do
>                     (tm' :=>: tv) <- elaborate True (tipTy :>: tm)
>                     give tm'
>         _  -> throwError' "give: only possible for incomplete goals."


> elabMake :: (String :<: INDTM) -> ProofState INTM
> elabMake (s :<: ty) = do
>     makeModule s
>     goIn
>     tt <- elaborate False (SET :>: ty)
>     tm <- moduleToGoal tt
>     goOut
>     return tm


> elabPiBoy :: (String :<: INDTM) -> ProofState ()
> elabPiBoy (s :<: ty) = do
>     tt <- elaborate True (SET :>: ty)
>     piBoy' (s :<: tt)
