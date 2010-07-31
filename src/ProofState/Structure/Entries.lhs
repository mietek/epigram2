\section{Managing Entries in a Development}
\label{sec:ProofState.Structure.Entries}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs , StandaloneDeriving #-}

> module ProofState.Structure.Entries where

> import Data.Traversable

> import NameSupply.NameSupply

> import Evidences.Tm

> import DisplayLang.Scheme

> import ProofState.Structure.Developments

%endif



\subsection{Looking into an |Entry|}

In the following, we define a bunch of helper functions to access
specific fields of an |Entry|. The field we look for might not exist
for all possible |Entry|, therefore we work in a |Maybe| world. The
naming rule of thumb of these function is: prefix |entry| followed by
the name of one field of the |E| or |M| cases, starting with a capital
letter.

Hence, we have:

> entryRef :: Traversable f => Entry f -> Maybe REF
> entryRef (EEntity r _ _ _)  = Just r
> entryRef (EModule _ _)      = Nothing
>
> entryName :: Traversable f => Entry f -> Name
> entryName (EEntity (n := _) _ _ _)  = n
> entryName (EModule n _)             = n
>
> entryLastName :: Traversable f => Entry f -> (String, Int)
> entryLastName (EEntity _ xn _ _)  = xn
> entryLastName (EModule n _)       = last n
>
> entryScheme :: Traversable f => Entry f -> Maybe (Scheme INTM)
> entryScheme (EDEF _ _ (PROG sch) _ _)  = Just sch
> entryScheme _                          = Nothing
>
> entryDev :: Traversable f => Entry f -> Maybe (Dev f)
> entryDev (EDEF _ _ _ d _)  = Just d
> entryDev (EModule _ d)     = Just d
> entryDev (EPARAM _ _ _ _)  = Nothing
>
> entrySuspendState :: Traversable f => Entry f -> SuspendState
> entrySuspendState e = case entryDev e of
>     Just dev  -> devSuspendState dev
>     Nothing   -> SuspendNone



\subsection{Entry equality}


Two entries are equal if and only if they have the same name:

> instance Traversable f => Eq (Entry f) where
>     e1 == e2 = entryName e1 == entryName e2



\subsection{Changing the carrier of an |Entry|}


The |entryCoerce| function is quite a thing. When defining |Dev|, we
have been picky in letting any Traversable |f| be the carrier of the
|f (Entry f)|. As shown in
Section~\ref{sec:ProofState.Edition.ProofContext}, we sometimes need
to jump from one Traversable |f| to another Traversable |g|. In this
example, we jump from a |NewsyFwd| -- a |Fwd| list -- to some
|Entries| -- a |Bwd| list.

Changing the type of the carrier is possible for parameters, in which
case we return a |Right entry|. It is not possible for definitions and
modules, in which case we return an unchanged |Left dev|.

> entryCoerce ::  (Traversable f, Traversable g) => 
>                 Entry f -> Either (Dev f) (Entry g)
> entryCoerce (EPARAM ref xn k ty)  =  Right $ EPARAM ref xn k ty
> entryCoerce (EDEF _ _ _ dev _)    =  Left dev
> entryCoerce (EModule _ dev)       =  Left dev


