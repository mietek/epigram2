\section{News about updated references}
\label{sec:Evidences.News}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module Evidences.News where

> import Prelude hiding (exp)

> import Control.Applicative
> import Control.Monad.Writer
> import Data.Traversable

> import Data.Foldable hiding (foldr)
> import Data.Maybe

> import Kit.BwdFwd

> import Evidences.Tm

%endif


The news system represents stored updates to references. For
performance reasons, we do not wish to traverse the entire proof state
every time modifications are made to one part of the tree. Instead, we
store news entries below the cursor, and update following entries when
the cursor moves down. This section describes the data that is stored
in the proof state, and section \ref{sec:Elaboration.Wire} describes
how news is propagated.


\subsection{News}


|News| represents possible changes to references. At the moment, it may
be |GoodNews| (the reference has become more defined) or |NoNews|
(even better from our perspective, as the reference has not
changed). Note that |News| is ordered by increasing ``niceness''.

When we come to implement functionality to remove definitions from the proof state,
we will also need |BadNews| (the reference has changed but is not more informative)
and |DeletedNews| (the reference has gone completely).

> data News = DeletedNews | BadNews | GoodNews | NoNews
>     deriving (Eq, Ord, Show)

Handily, |News| is a monoid where the neutral element is |NoNews| and composing
two |News| takes the less nice.

> instance Monoid News where
>     mempty   = NoNews
>     mappend  = min


> data BoyNews = BadBoyNews TY | GoodBoyNews TY | NoBoyNews
>     deriving (Show)

> instance Monoid BoyNews where
>     mempty                 = NoBoyNews
>     NoBoyNews `mappend` n  = n
>     n `mappend` NoBoyNews  = n
>     GoodBoyNews t1 `mappend` GoodBoyNews t2 = GoodBoyNews t1
>     -- do bad boy news soon

> toBoyNews :: News -> TY -> BoyNews
> toBoyNews NoNews    _   = NoBoyNews
> toBoyNews GoodNews  ty  = GoodBoyNews ty
> toBoyNews BadNews   ty  = BadBoyNews ty

\subsection{News Bulletin}

A |NewsBulletin| is a list of pairs of updated references and the news about them.

> type GirlNewsBulletin  = [(DEF, News)]
> type BoyNewsBulletin   = Maybe (Bwd BoyNews)
> type NewsBulletin      = (GirlNewsBulletin, BoyNewsBulletin)

> noBoyNews :: Int -> Bwd BoyNews
> noBoyNews i = bwdList (replicate i NoBoyNews)

> pattern NONEWS = ([], Nothing)

> boring :: NewsBulletin -> Bool
> boring NONEWS  = True
> boring _       = False

\subsubsection{Adding news}

The |addNews| function adds the given news to the bulletin, if it is newsworthy.

> addGirlNews :: (DEF, News) -> NewsBulletin ->  NewsBulletin
> addGirlNews dn (gns, bns) = (addNews dn gns, bns)

> addNews :: (DEF, News) -> GirlNewsBulletin ->  GirlNewsBulletin
> addNews (_,  NoNews)  old  = old
> addNews (r,  n)       old  = (r, n `mappend` n') : old' where
>   -- Find previous versions n' (if any), 
>   -- Remove duplicate in old':
>   (n', old') = seek old
>   seek [] = (NoNews, [])
>   seek ((r', n') : old) | r == r' = (n', old)
>   seek (rn : old) = (n', rn : old') where (n', old') = seek old

Using |seek|, we enforce the invariant that any reference
appears at most once in a |NewsBulletin|.


< addBoyNews :: (Int, BoyNews) -> NewsBulletin -> NewsBulletin
< addBoyNews (_, NoBoyNews) news = news
< addBoyNews (l, bn) (gs, bs) =
<     (gs, bwdInsertAt (bwdLength bs - l - 1) bn bs)
<   where
<     bwdInsertAt :: Int -> a -> Bwd a -> Bwd a
<     bwdInsertAt 0 a (bs :< _) = bs :< a
<     bwdInsertAt n a (bs :< b) = bwdInsertAt (n-1) a bs :< b



\subsubsection{Getting the latest news}

The |lookupNews| function returns the news about a reference contained
in the bulletin, which may be |NoNews| if the reference is not
present.

> lookupNews :: NewsBulletin -> DEF -> News
> lookupNews (nb, _) ref = fromMaybe NoNews (lookup ref nb)

> lookupBoyNews :: NewsBulletin -> Int -> BoyNews
> lookupBoyNews (_, Nothing) _ = NoBoyNews
> lookupBoyNews (_, Just bs) l = case bs !. (bwdLength bs - 1 - l) of
>     Just bn  -> bn
>     Nothing  -> error $ "lookupBoyNews: missing news about boy " ++ show l


The |getNews| function looks for a reference in the news bulletin,
and returns it with its news if it is found, or returns |Nothing| if
not.

> getNews :: NewsBulletin -> DEF -> Maybe (DEF, News)
> getNews (nb, _) ref = find ((== ref) . fst) nb

> getBoyNews :: NewsBulletin -> (Int, String, TY) -> Writer News (Int, String, TY)
> getBoyNews bull (l, s, t) = case lookupBoyNews bull l of
>     NoBoyNews       -> pure (l, s, t)
>     GoodBoyNews t'  -> tell GoodNews >> pure (l, s, t')
>     BadBoyNews t'   -> tell BadNews >> pure (l, s, t')

The |getLatest| function returns the most up-to-date copy of the given
reference, either the one from the bulletin if it is present, or the
one passed in otherwise. If given a |FAKE| reference, it will always
return one, regardless of the status of the reference in the bulletin.
This ensures that fake references in labels have their types updated
without turning into real definitions unexpectedly.

> getLatest :: NewsBulletin -> DEF -> DEF
> getLatest ([], _)              ref = ref
> getLatest ((ref', _):news, _)  ref
>     | ref == ref'  = ref'
>     | otherwise    = getLatest (news, Nothing) ref



\subsubsection{Merging news}


The |mergeNews| function takes older and newer bulletins, and composes them to
produce a single bulletin with the worst news about every reference mentioned
in either.

> mergeNews :: NewsBulletin -> NewsBulletin -> NewsBulletin
> mergeNews new NONEWS = new
> mergeNews (newg, newb) (oldg, oldb) =
>     (foldr addNews oldg newg, mergeBoyNews newb oldb)


> mergeBoyNews (Just newb) (Just oldb)  = Just (bwdZipWith mappend newb oldb)
> mergeBoyNews (Just newb) Nothing      = Just newb
> mergeBoyNews Nothing     (Just oldb)  = Just oldb
> mergeBoyNews Nothing     Nothing      = Nothing



\subsubsection{Read all about it}

The |tellNews| function applies a bulletin to a term. It returns the updated
term and the news about it (i.e.\ the least nice news of any reference used
in the term). Using the |Writer| monad allows the term to be updated and the
news about it calculated in a single traversal. Note that we ensure |FAKE|
references remain as they are, as in |getLatest|.

> tellNews :: NewsBulletin -> EXP -> (EXP, News)
> tellNews NONEWS tm = (tm, NoNews)
> tellNews bull   tm = runWriter $ traverseTm tm
>   where
>     traverseTm :: Tm {p, s, n} -> Writer News (Tm {Body, Exp, n})
>     traverseTm (L g x b) = (| L (traverseEnv g) ~x (traverseTm b) |)
>     traverseTm (LK b) = (| LK (traverseTm b) |)
>     traverseTm (c :- es) = (| (c :-) (traverse traverseTm es) |)
>     traverseTm (f :$ as) = (| ((ENil :/) <$> traverseTm f) :$ (traverse (traverse traverseTm) as) |)
>     traverseTm (D d) = do
>         case (getNews bull d) of
>           Nothing         -> pure (D d :$ B0)
>           (Just (d', n))  -> tell n >> pure (D d' :$ B0) 
>     traverseTm (B (SIMPLDTY na _I uDs)) = do
>       _I' <- traverseTm _I
>       uDs' <- traverseTm uDs
>       return $ B (SIMPLDTY na _I' uDs') :$ B0
>     traverseTm (V i) = (| (V i :$ B0) |)
>     traverseTm (P lst) = (| (| P (getBoyNews bull lst) |) :$ ~B0 |)
>     traverseTm (Refl _X x) = do
>       _X' <- traverseTm _X 
>       x' <- traverseTm x
>       return (Refl _X' x' :$ B0) 
>     traverseTm (Coeh coeh _X _Y p x) = do
>       _X' <- traverseTm _X
>       _Y' <- traverseTm _Y 
>       p' <- traverseTm p
>       x' <- traverseTm x
>       return (Coeh coeh _X' _Y' p' x' :$ B0) 
>     traverseTm (g :/ t) = (| (traverseEnv g) :/ (traverseTm t) |)
>
>     traverseEnv :: Env {n} {m} -> Writer News (Env {n} {m})
>     traverseEnv (lev, iev) = 
>       (| (traverse (\ (i,x) -> (| (\t -> (i,t)) (traverseTm x) |)) lev)
>                                  , traverseIEnv iev |)

>     traverseIEnv :: IEnv {n, m} -> Writer News (IEnv {n, m})
>     traverseIEnv INix = pure INix
>     traverseIEnv INil = pure INil
>     traverseIEnv (g :<<: t) = (| (traverseIEnv g) :<<: traverseTm t |)
