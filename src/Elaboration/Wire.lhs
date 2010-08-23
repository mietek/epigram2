\section{Wire Service}
\label{sec:Elaboration.Wire}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, PatternGuards #-}

> module Elaboration.Wire where

> import Control.Applicative

> import Kit.BwdFwd

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import ProofState.Edition.ProofContext
> import ProofState.Edition.News
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.Scope

> import ProofState.Interface.Lifting
> import ProofState.Interface.ProofKit

> import Evidences.Tm
> import Evidences.Eval

> import Elaboration.ElabMonad

> import Kit.MissingLibrary

%endif


Here we describe how to handle updates to references in the proof state, caused by
refinement commands like |give|. The idea is to deal with updates lazily, to avoid
unnecessary traversals of the proof tree. When |updateRef| is called to announce
a changed reference (that the current development has already processed), it simply
inserts a news bulletin below the current development.

> updateRef :: REF -> ProofState ()
> updateRef ref = putNewsBelow [(ref, GoodNews)]


The |propagateNews| function takes a current news bulletin and a list of entries
to add to the current development. It applies the news bulletin to each entry
in turn, picking up other bulletins along the way. This function should be called
when navigating to a development that may contain news bulletins, so they can be
pushed out of sight.

> propagateNews :: Bool -> NewsBulletin -> NewsyEntries -> ProofState NewsBulletin

If we have nothing to say and nobody to tell, we might as well give up and go home.

> propagateNews _ [] (NF F0) = return []

> propagateNews False news (NF F0) = return news

If there are no entries to process, we should tell the current entry
(if there is one), stash the bulletin after the current location and
stop. Note that the insertion is optional because it will fail when we
have reached the end of the module, at which point everyone knows the
news anyway.

> propagateNews True news (NF F0) = do
>     news' <- tellCurrentEntry news
>     optional (putNewsBelow news')
>     return news'

A |Parameter| is relatively easy to deal with, we just check to see if
its type has become more defined, and pass on the good news if
necessary.

> propagateNews top news (NF (Right (EPARAM (name := DECL :<: tv) sn k ty) :> es)) = do
>     case tellNews news ty of
>         (_, NoNews) -> putEntryAbove (EPARAM (name := DECL :<: tv) sn k ty) >> propagateNews top news (NF es)
>         (ty', GoodNews) -> do
>             let ref = name := DECL :<: evTm ty'
>             putEntryAbove (EPARAM ref sn k ty')
>             propagateNews top (addNews (ref, GoodNews) news) (NF es)

Updating definitions is a bit more complicated. We proceed as follows:
\begin{enumerate}
\item Add the definition to the context, using |jumpIn|.
\item Recursively propagate the news to the children.
\item Call |tellCurrentEntry| to update the definition itself.
\item Continue propagating the latest news.
\end{enumerate}

> propagateNews top news (NF ((Right e@(EDEF ref sn _ _ ty)) :> es)) = do
>     xs <- jumpIn e
>     news' <- propagateNews False news xs
>     news'' <- tellCurrentEntry news'
>     goOut
>     propagateNews top news'' (NF es)

Modules do not carry type information so all we need to do is propagate
the news to their children.

> propagateNews top news (NF (Right e@(EModule n d) :> es)) = do
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
>     Dev es tip nsupply ss <- getAboveCursor
>     below <- getBelowCursor
>     putLayer (Layer es (mkCurrentEntry e) (reverseEntries below) tip nsupply ss)
>     let Just (Dev cs newTip newNSupply newSS) = entryDev e
>     putAboveCursor (Dev B0 newTip newNSupply newSS)
>     return cs


The |tellEntry| function informs an entry about a news bulletin that
its children have already received. If the entry is a definition, she
must be the current entry of the current cursor position (i.e. the
entry should come from getLeaveCurrent).

> tellEntry :: NewsBulletin -> Entry Bwd -> ProofState (NewsBulletin, Entry Bwd)

Modules carry no type information, so they are easy:

> tellEntry news (EModule n d) = return (news, EModule n d)

To update a parameter, we must:
\begin{enumerate}
\item update the overall type of the entry, and
\item update the news bulletin with news about this definition.
\end{enumerate}

> tellEntry news (EPARAM (name := DECL :<: tv) sn k ty) = do
>     let (ty' :=>: tv', n)  = tellNewsEval news (ty :=>: tv)
>     let ref = name := DECL :<: tv'
>     return (addNews (ref, n) news, EPARAM ref sn k ty')

To update a hole, we must first check to see if the news bulletin contains a
definition for it. If so, we fill in the definition (and do not need to
update the news bulletin). If not, we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference; and
\item update the news bulletin with news about this definition.
\end{enumerate}
If the hole is |Hoping| and we have good news about its type, then we
restart elaboration to see if it can make any progress.

> tellEntry news (EDEF ref@(name := HOLE h :<: tyv) sn
>                      dkind dev@(Dev {devTip=Unknown tt}) ty)
>   | Just (ref'@(_ := DEFN tm :<: _), GoodNews) <- getNews news ref = do
>     es   <- getInScope
>     tm'  <- bquoteHere (tm $$$ paramSpine es)
>     let  (tt', _) = tellNewsEval news tt
>          (ty', _) = tellNews news ty
>     return (news, EDEF ref' sn dkind (dev{devTip=Defined tm' tt'}) ty')
>
>   | otherwise = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE h :<: tyv'
>          tip                  = case (min n n', h) of
>                                     (GoodNews, Hoping)  -> Suspended tt' ElabHope
>                                     _                   -> Unknown tt'
>     return (addNews (ref, min n n') news,
>         EDEF ref sn dkind (dev{devTip=tip}) ty')

To update a hole with a suspended elaboration problem attached, we proceed
similarly to the previous case, but we also update the elaboration problem.
If the news bulletin defines this hole, it had better just be hoping for
a solution, in which case we can safely ignore the attached |ElabHope| process.

> tellEntry news (EDEF  ref@(name := HOLE h :<: tyv) sn
>                       dkind dev@(Dev {devTip=Suspended tt prob}) ty)
>   | Just ne <- getNews news ref = case prob of
>       ElabHope  -> tellEntry news (EDEF ref sn dkind (dev{devTip=Unknown tt}) ty)
>       _         -> throwError' . err . unlines $ [
>                     "tellEntry: news bulletin contains update", show ne,
>                     "for hole", show ref,
>                     "with suspended computation", show prob]
>   | otherwise = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE h :<: tyv'
>          prob'                = tellEProb news prob
>     suspendHierarchy (if isUnstable prob' then SuspendUnstable else SuspendStable)
>     return (addNews (ref, min n n') news,
>         EDEF ref sn dkind (dev{devTip=Suspended tt' prob'}) ty')

To update a closed definition (|Defined|), we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference;
\item update the definition and re-evaluate it
         (\question{could this be made more efficient?}); and
\item update the news bulletin with news about this definition.
\end{enumerate}

> tellEntry news (EDEF (name := DEFN tmL :<: tyv) sn dkind dev@(Dev {devTip=Defined tm tt}) ty) = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          (tm', n'')           = tellNews news tm
>     aus <- getGlobalScope
>     let tmL' = parBind aus (devEntries dev) tm'

For paranoia purposes, the following test might be helpful:

<     mc <- withNSupply (inCheck $ check (tyv' :>: tmL'))
<     mc `catchEither` unlines ["tellEntry " ++ showName name ++ ":",
<                                 show tmL', "is not of type", show ty' ]

>     let ref = name := DEFN (evTm tmL') :<: tyv'
>     return (addNews (ref, GoodNews {-min (min n n') n''-}) news,
>                 EDEF ref sn dkind (dev{devTip=Defined tm' tt'}) ty')

The |tellCurrentEntry| function informs the current entry about a news
bulletin that her children have already received, and returns the
updated news.

> tellCurrentEntry :: NewsBulletin -> ProofState NewsBulletin
> tellCurrentEntry news = do
>     e <- getLeaveCurrent
>     (news', e') <- tellEntry news e 
>     putEnterCurrent e'
>     return news'


> tellEProb :: NewsBulletin -> EProb -> EProb
> tellEProb news = fmap (getLatest news)




When the current location or one of its children has suspended, we need to
update the outer layers.

> suspendHierarchy :: SuspendState -> ProofState ()
> suspendHierarchy ss = getLayers >>= putLayers . help ss
>   where
>     help :: SuspendState -> Bwd Layer -> Bwd Layer
>     help ss B0 = B0
>     help ss (ls :< l) = help ss' ls :< l{laySuspendState = ss'}
>       where ss' = min ss (laySuspendState l)