\section{Relabelling}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Tactics.Relabel where

> import Control.Applicative
> import Control.Monad.State

> import Evidences.Rules
> import Evidences.Tm

> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm


> import Kit.MissingLibrary

%endif

> relabel :: [InDTmRN] -> ProofState ()
> relabel ts = do
>     _ :=>: LABEL (N l) ty <- getHoleGoal
>     let Just (r, as) = splitSpine l
>     n <- matchArgs (pty r) (P r) as ts
>     ty' <- bquoteHere ty
>     g :=>: _ <- make ("g" :<: LABEL (N n) ty')
>     give' (N g)
>     goIn
>   where
>     splitSpine :: NEU -> Maybe (REF, [VAL])
>     splitSpine (P r) = return (r, [])
>     splitSpine (n :$ A a) = do
>         (r, as) <- splitSpine n
>         return (r, as ++ [a])
>     splitSpine _ = (|)

>     matchArgs :: TY -> EXTM -> [VAL] -> [InDTmRN] -> ProofState EXTM
>     matchArgs _ n []  []  = return n
>     matchArgs _ _ []  _   = throwError' $ err "relabel: too many arguments!"
>     matchArgs _ _ _   []  = throwError' $ err "relabel: too few arguments!"
>     matchArgs (PI s t) n (a:as) (w : ws) = do
>         tm :=>: _ <- mapStateT (either (Left . (fmap $ fmap $ fmap fst)) Right)
>                          (match (s :>: (w, a)))
>         matchArgs (t $$ A a) (n :$ A tm) as ws
>     matchArgs ty n as ts = throwError' $ err "relabel: unmatched\nty ="
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "\nn =" ++ errInTm (N n)
>                              ++ err "\nas =" ++ map UntypedVal as
>                              ++ err "\nts =" ++ map UntypedTm ts

>     match :: TY :>: (InDTmRN, VAL) -> ProofStateT (InDTmRN, VAL) (INTM :=>: VAL)
>     match (ty :>: (DNP [(x, Rel 0)], a)) =
>         mapStateT (either (Left . error "oh no") Right) $ do
>             ty'  <- bquoteHere ty
>             a'   <- bquoteHere a
>             make (x :<: ty')
>             goIn
>             neutralise =<< give a'
>     match (C cty :>: (DC dc, C cv)) = case halfZip dc cv of
>        Just c   -> do
>            c' <- canTy match (cty :>: c)
>            return $ C (fmap termOf c') :=>: C (fmap valueOf c')
>        Nothing  -> throwError' $ err "relabel: halfzip failed!"
>         

> import -> CochonTactics where
>   : simpleCT "relabel" (| bwdList (some (|InArg (sizedInDTm minBound)|)) |)
>       (\ as -> relabel (map argToIn as) >> return "Relabelled.")
>       "relabel <args> - changes names of arguments in label"