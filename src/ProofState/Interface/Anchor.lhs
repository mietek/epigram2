\section{Anchor resolution}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Anchor where

> import Control.Applicative
> import Control.Monad

> import Data.Foldable
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd

> import NameSupply.NameSupply

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.Scope

> import Evidences.Tm

> import DisplayLang.Name

%endif

> isAnchor :: Traversable f => Entry f -> Bool
> isAnchor (EEntity _ _ _ _ (Just _))  = True
> isAnchor _                           = False

> anchorsInScope :: ProofState Entries
> anchorsInScope = do
>   scope <- getInScope 
>   return $ foldMap anchors scope
>       where anchors t | isAnchor t = B0 :< t
>                       | otherwise  = B0

To cope with shadowing, we will need some form of |RelativeAnchor|:

< type RelativeAnchor = (Anchor, Int)

With shadowing punished by De Bruijn. Meanwhile, let's keep it simple.

> resolveAnchor :: Anchor -> ProofState (Maybe REF)
> resolveAnchor anchor = do
>   scope <- getInScope
>   case foldMap (resolveAnchor' anchor) scope of
>     B0          -> return Nothing
>     (_ :< ref)  -> return $ Just ref
>     where resolveAnchor' :: Anchor -> Entry Bwd -> Bwd REF
>           resolveAnchor' anchor (EEntity _ _ _ _ Nothing) = B0
>           resolveAnchor' anchor (EEntity r _ _ _ (Just anchor'))
>               | anchor == anchor' = B0 :< r
>               | otherwise = B0
>           resolveAnchor' anchor (EModule _ _) = B0

Find the entry corresponding to the given anchor:

> findAnchor :: Anchor -> ProofState ()
> findAnchor = undefined

Redefine the entry corresponding from the given anchor, so that's name
is the second anchor:

> renameAnchor :: Anchor -> Anchor -> ProofState ()
> renameAnchor = undefined