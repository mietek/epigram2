\section{Entries manipulation}
\label{sec:entries}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs , StandaloneDeriving #-}

> module ProofState.Structure.Entries where

> import Data.Foldable
> import Data.List
> import Data.Traversable

> import Kit.BwdFwd

> import NameSupply.NameSupply

> import Evidences.Tm

> import Elaboration.ElabMonad

> import DisplayLang.Scheme

> import ProofState.Structure.Developments

%endif


\pierre{This section is a complete mess. Structure is needed.}


We often need to turn the sequence of boys (parameters) under which we
work into the argument spine of a \(\lambda\)-lifted definition:

> boySpine :: Entries -> Spine {TT} REF
> boySpine = foldMap boy where
>   boy :: Entry Bwd -> Spine {TT} REF
>   boy (EPARAM r _ _ _)   = [A (N (P r))]
>   boy _                  = []

> boyREFs :: Entries -> [REF]
> boyREFs = foldMap boy where
>   boy :: Entry Bwd -> [REF]
>   boy (EPARAM r _ _ _)   = [r]
>   boy _                  = []




In the following, we define a handful of functions which are quite
handy, yet not grandiose. This section can be skipped on a first
reading.

We sometimes wish to determine whether an entry is a |Parameter|:

> isBoy :: Traversable f => Entry f -> Bool
> isBoy (EPARAM _ _ _ _)  = True
> isBoy _                  = False

> entryREF :: Traversable f => Entry f -> Maybe REF
> entryREF (E r _ _ _)  = Just r
> entryREF (M _ _)      = Nothing

Given an |Entry|, a natural operation is to extract its
sub-developments. This works for girls and modules, but will not for
boys.

> entryDev :: Traversable f => Entry f -> Maybe (Dev f)
> entryDev (EPARAM _ _ _ _)  = Nothing
> entryDev (EDEF _ _ _ d _)  = Just d
> entryDev (M _ d)           = Just d

For display purposes, we often ask the last name or the whole name of
an |Entry|:

> entryLastName :: Traversable f => Entry f -> (String, Int)
> entryLastName (E _ xn _ _)  = xn
> entryLastName (M n _)       = last n
>
> entryName :: Traversable f => Entry f -> Name
> entryName (E (n := _) _ _ _)  = n
> entryName (M n _)             = n

Some girls have |Scheme|s, and we can extract them thus:

> kindScheme :: DefKind -> Maybe (Scheme INTM)
> kindScheme LETG        = Nothing
> kindScheme (PROG sch)  = Just sch
>
> entryScheme :: Traversable f => Entry f -> Maybe (Scheme INTM)
> entryScheme (EDEF _ _ k _ _)  = kindScheme k
> entryScheme _                 = Nothing

The |entryCoerce| function is quite a thing. When defining |Dev|, we
have been picky in letting any Traversable |f| be the carrier of the
|f (Entry f)|. As shown in Section~\ref{sec:proof_context}, we
sometimes need to jump from one Traversable |f| to another Traversable
|g|. In this example, we jump from a |NewsyFwd| -- a |Fwd| list -- to
some |Entries| -- a |Bwd| list.

Changing the type of the carrier is possible for boys, in which case
we return a |Right entry|. It is not possible for girls and modules,
in which case we return an unchanged |Left dev|.

> entryCoerce ::  (Traversable f, Traversable g) => 
>                 Entry f -> Either (Dev f) (Entry g)
> entryCoerce (EPARAM ref xn k ty)  = Right $ EPARAM ref xn k ty
> entryCoerce (EDEF _ _ _ dev _)    = Left dev
> entryCoerce (M _    dev)          = Left dev

We can extract the |SuspendState| from an entry, noting that boys do not have
children so cannot contain suspended elaboration processes.

> entrySuspendState :: Traversable f => Entry f -> SuspendState
> entrySuspendState e = case entryDev e of
>     Just dev  -> devSuspendState dev
>     Nothing   -> SuspendNone


Finally, we can compare entities for equality by comparing their
names.

> instance Traversable f => Eq (Entry f) where
>     e1 == e2 = entryName e1 == entryName e2

