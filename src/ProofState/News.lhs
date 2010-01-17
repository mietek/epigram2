\section{News about updated references}
\label{sec:news}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.News where

> import Data.List
> import Data.Maybe
> import Data.Monoid hiding (All)

> import Evidences.Tm

%endif


|News| represents possible changes to references. At the moment, it may be |GoodNews|
(the reference has become more defined) or |NoNews| (even better from our perspective,
as the reference has not changed). Note that |News| is ordered by increasing ``niceness''.

When we come to implement functionality to remove definitions from the proof state,
we will also need |BadNews| (the reference has changed but is not more informative)
and |DeletedNews| (the reference has gone completely).

> data News = DeletedNews | BadNews | GoodNews | NoNews deriving (Eq, Ord, Show)

> instance Monoid News where
>     mempty   = NoNews
>     mappend  = min

A |NewsBulletin| is a list of pairs of updated references and the news about them.

> type NewsBulletin = [(REF, News)]

The |addNews| function adds the given news to the bulletin, if it is newsworthy.
Conor made it delete old versions but minimize news goodness.

> addNews :: (REF, News) -> NewsBulletin ->  NewsBulletin
> addNews (_,  NoNews)  old  = old
> addNews (r,  n)       old  = (r, min n n') : old' where
>   (n', old') = seek old
>   seek [] = (NoNews, [])
>   seek ((r', n') : old) | r == r' = (n', old)
>   seek (rn : old) = (n', rn : old') where (n', old') = seek old

The |lookupNews| function returns the news about a reference contained in the
bulletin, which may be |NoNews| if the reference is not present.

> lookupNews :: NewsBulletin -> REF -> News
> lookupNews nb ref = fromMaybe NoNews (lookup ref nb)

The |getLatest| function returns the most up-to-date copy of the given reference,
either the one from the bulletin if it is present, or the one passed in otherwise.
The slightly odd recursive case arises because equality for references just compares
their names.

> getLatest :: NewsBulletin -> REF -> REF
> getLatest []                ref = ref
> getLatest ((ref', _):news)  ref
>     | ref == ref'  = ref'
>     | otherwise    = getLatest news ref

\conor{Need to modify this to update FAKEs correctly.}

The |mergeNews| function takes older and newer bulletins, and composes them to
produce a single bulletin with the worst news about every reference mentioned
in either.

> mergeNews :: NewsBulletin -> NewsBulletin -> NewsBulletin
> mergeNews new [] = new
> mergeNews new old = Data.List.foldr addNews old new

