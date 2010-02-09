\section{Wire Service}
\label{sec:wire_service}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Wire where

> import Control.Applicative
> import Data.Foldable

> import Kit.BwdFwd

> import ProofState.Developments
> import ProofState.News
> import ProofState.Lifting
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import Evidences.Tm
> import Evidences.Rules

> import DisplayLang.ElabMonad

%endif


Here we describe how to handle updates to references in the proof state, caused by
refinement commands like |give|. The idea is to deal with updates lazily, to avoid
unnecessary traversals of the proof tree. When |updateRef| is called to announce
a changed reference (that the current development has already processed), it simply
inserts a news bulletin below the current development.

> updateRef :: REF -> ProofState ()
> updateRef ref = insertCadet [(ref, GoodNews)]


The |propagateNews| function takes a current news bulletin and a list of entries
to add to the current development. It applies the news bulletin to each entry
in turn, picking up other bulletins along the way. This function should be called
when navigating to a development that may contain news bulletins, so they can be
pushed out of sight.

> propagateNews :: Bool -> NewsBulletin -> NewsyEntries -> ProofState NewsBulletin

If we have nothing to say and nobody to tell, we might as well give up and go home.

> propagateNews _ [] (NF F0) = return []

> propagateNews False news (NF F0) = return news

If there are no entries to process, we should tell the mother (if there is one),
stash the bulletin after the current location and stop. Note that the insertion is
optional because it will fail when we have reached the end of the module, at which
point everyone knows the news anyway.

> propagateNews True news (NF F0) = do
>     news' <- tellMother news
>     optional (insertCadet news')
>     return news'

A |Boy| is relatively easy to deal with, we just check to see if its type
has become more defined, and pass on the good news if necessary.

> propagateNews top news (NF (Right (E (name := DECL :<: tv) sn (Boy k) ty) :> es)) = do
>     case tellNews news ty of
>         (_, NoNews) -> putDevEntry (E (name := DECL :<: tv) sn (Boy k) ty) >> propagateNews top news (NF es)
>         (ty', GoodNews) -> do
>             let ref = name := DECL :<: evTm ty'
>             putDevEntry (E ref sn (Boy k) ty')
>             propagateNews top (addNews (ref, GoodNews) news) (NF es)

Updating girls is a bit more complicated. We proceed as follows:
\begin{enumerate}
\item Add the girl to the context, using |jumpIn|.
\item Recursively propagate the news to the children.
\item Call |tellMother| to update the girl herself.
\item Continue propagating the latest news.
\end{enumerate}

> propagateNews top news (NF ((Right e@(E ref sn (Girl LETG (_, tip, nsupply) _) ty)) :> es)) = do
>     xs <- jumpIn e
>     news' <- propagateNews False news xs
>     news'' <- tellMother news'
>     goOut
>     propagateNews top news'' (NF es)

Modules do not carry type information so all we need to do is propagate
the news to their children.

> propagateNews top news (NF (Right e@(M n d) :> es)) = do
>     xs <- jumpIn e
>     news' <- propagateNews False news xs
>     goOut
>     propagateNews top news (NF es)


Finally, if we encounter an older news bulletin when propagating news, we can simply
merge the two together.

> propagateNews top news (NF (Left oldNews :> es)) =
>   propagateNews top (mergeNews news oldNews) (NF es)


The |jumpIn| command adds the given entry at the cursor position without
its children, moves the focus inside it and returns its children. This is
a slightly strange thing to do, but is useful for news propagation.

> jumpIn :: Entry NewsyFwd -> ProofState NewsyEntries
> jumpIn e = do
>     (es, tip, nsupply) <- getDev
>     cadets <- getDevCadets
>     putLayer (Layer es (entryToMother e) (reverseEntries cadets) tip nsupply)
>     let Just (cs, newTip, newNSupply) = entryDev e
>     putDev (B0, newTip, newNSupply)
>     return cs


The |tellEntry| function informs an entry about a news bulletin that its
children have already received. If the entry is a girl, she must be the
mother of the current cursor position (i.e. the entry should come from
getMotherEntry).

> tellEntry :: NewsBulletin -> Entry Bwd -> ProofState (NewsBulletin, Entry Bwd)

Modules carry no type information, so they are easy:

> tellEntry news (M n d) = return (news, M n d)

To update a boy, we must:
\begin{enumerate}
\item update the overall type of the entry, and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellEntry news (E (name := DECL :<: tv) sn (Boy k) ty) = do
>     let (ty' :=>: tv', n)  = tellNewsEval news (ty :=>: tv)
>     let ref = name := DECL :<: tv'
>     return (addNews (ref, n) news, E ref sn (Boy k) ty')

To update a hole, we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference; and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellEntry news (E (name := HOLE h :<: tyv) sn (Girl LETG (cs, Unknown tt, nsupply) ms) ty) = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE h :<: tyv'
>     return (addNews (ref, min n n') news,
>         E ref sn (Girl LETG (cs, Unknown tt', nsupply) ms) ty')

> tellEntry news (E (name := HOLE h :<: tyv) sn (Girl LETG (cs, UnknownElab tt elab, nsupply) ms) ty) = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE h :<: tyv'
>     return (addNews (ref, min n n') news,
>         E ref sn (Girl LETG (cs, UnknownElab tt' elab, nsupply) ms) ty')

To update a defined girl, we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference;
\item update the definition and re-evaluate it
         (\question{could this be made more efficient?}); and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellEntry news (E (name := DEFN tmL :<: tyv) sn (Girl LETG (cs, Defined tm tt, nsupply) ms) ty) = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          (tm', n'')           = tellNews news tm
>     aus <- getGreatAuncles
>     let tmL' = parBind aus cs tm'

For paranoia purposes, the following test might be helpful:

<     mc <- withNSupply (inCheck $ check (tyv' :>: tmL'))
<     mc `catchEither` unlines ["tellEntry " ++ showName name ++ ":",
<                                 show tmL', "is not of type", show ty' ]

>     let ref = name := DEFN (evTm tmL') :<: tyv'
>     return (addNews (ref, GoodNews {-min (min n n') n''-}) news,
>                 E ref sn (Girl LETG (cs, Defined tm' tt', nsupply) ms) ty')

The |tellMother| function informs the mother entry about a news bulletin
that her children have already received, and returns the updated news.

> tellMother :: NewsBulletin -> ProofState NewsBulletin
> tellMother news = do
>     e <- getMotherEntry
>     (news', e') <- tellEntry news e 
>     putMotherEntry e'
>     tip <- getDevTip
>     case tip of
>         UnknownElab tt elab -> do
>             melab <- tellElab news elab
>             case melab of
>                 Just elab' -> do
>                     putDevTip (Unknown tt)
>                     proofTrace $ "tellMother: resuming elaboration on "
>                         ++ show (entryName e') ++ ":\n" ++ show elab'
>                     mtm <- runElab elab'
>                     case mtm of
>                         Just (tm :=>: _ ) -> give' tm >> return ()
>                         Nothing -> proofTrace
>                             "tellMother: elaboration suspended."
>                 Nothing -> return ()
>         _ -> return ()
>     return news'


> tellElab :: NewsBulletin -> Elab VAL -> ProofState (Maybe (Elab VAL))
> tellElab news (Bale v) = do
>     v' <- bquoteHere v
>     case tellNews news v' of
>         (v'', GoodNews)  -> return . Just . Bale . evTm $ v''
>         (_, NoNews)      -> return Nothing
> tellElab news (ECan v f) = do
>     v' <- bquoteHere v
>     case tellNews news v' of
>         (v'', GoodNews)  -> return $ Just (ECan (evTm v'') f)
>         (_, NoNews)      -> return Nothing
> tellElab news elab = return $ Just elab