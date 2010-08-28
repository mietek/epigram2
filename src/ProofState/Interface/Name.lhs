\section{Name management}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Name where

> import Data.Foldable

> import NameSupply.NameSupply

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import Evidences.Tm
> import Evidences.Operators


%endif



The |lookupName| function looks up a name in the context (including axioms and
primitives); if found, it returns the reference applied to the spine of
shared parameters.

> lookupName :: Name -> ProofStateT e (Maybe (EXTM :=>: VAL))
> lookupName name = do
>     inScope <- getInScope
>     case find ((name ==) . entryName) inScope of
>       Just (EEntity ref _ _ _ _)  -> return $ Just $ applySpine ref inScope
>       Nothing             ->
>         case find ((name ==) . refName . snd) primitives of
>           Just (_, ref)  -> return $ Just $ applySpine ref inScope
>           Nothing        -> return Nothing



The |pickName| command takes a prefix suggestion and a name suggestion
(either of which may be empty), and returns a more-likely-to-be-unique
name if the name suggestion is empty.

> pickName :: String -> String -> ProofState String
> pickName "" s = pickName "x" s
> pickName prefix ""  = do
>     m <- getCurrentName
>     r <- getDevNSupply
>     return $ prefix ++ show (foldMap snd m + snd r)
> pickName _ s   = return s
