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

> import Elaboration.ElabProb

> import Kit.MissingLibrary

%endif

\subsection{Updating a reference}

Here we describe how to handle updates to references in the proof
state, caused by refinement commands like |give|. The idea is to deal
with updates lazily, to avoid unnecessary traversals of the proof
tree. When |updateRef| is called to announce a changed reference (that
the current development has already processed), it simply inserts a
news bulletin below the current development.

> updateRef :: REF -> ProofState ()
> updateRef ref = putNewsBelow [(ref, GoodNews)]


\subsection{Committing news into the ProofState}

The |propagateNews| function takes a current news bulletin and a list
of entries to \emph{add} to the current development. It applies the
news bulletin to each entry in turn, picking up other bulletins along
the way. This function is called when navigating to a development that
may contain news bulletins, so they can be pushed out of sight.

> propagateNews :: PropagateStatus ->  NewsBulletin -> NewsyEntries -> 
>                                      ProofState NewsBulletin

We need to keep track of whether news propagation was called normally or as a
recursive call. If called normally, we will stash the news bulletin the proof
state when done, but this is unnecessary if news propagation will continue
outside the recursive call.

> data PropagateStatus = NormalPropagate | RecursivePropagate

If we have nothing to say and nobody to tell, we might as well give up
and go home. If we were called recursively and have nobody to listen to
the news, we give up as well.

> propagateNews _ [] (NF F0) = return []
> propagateNews RecursivePropagate news (NF F0) = return news

If there are no entries to process, we should tell the current entry
(there is one, as we are within a development), stash the bulletin
after the current location and stop. Note that the insertion is
optional because it will fail when we have reached the end of the
module, at which point everyone knows the news anyway.

> propagateNews NormalPropagate news (NF F0) = do
>     news' <- tellCurrentEntry news
>     optional (putNewsBelow news')
>     return news'

To update a |Parameter|, we check to see if its type has become more defined,
and pass on the good news if necessary.

> propagateNews  top news 
>                (NF (Right (EPARAM (name := DECL :<: tv) sn k ty a) :> es)) = do
>     case tellNews news ty of
>         (_, NoNews) -> do
>           let ref = name := DECL :<: tv
>           putEntryAbove (EPARAM ref sn k ty a) 
>           propagateNews top news (NF es)
>         (ty', GoodNews) -> do
>           let ref = name := DECL :<: evTm ty'
>           putEntryAbove (EPARAM ref sn k ty' a)
>           propagateNews top (addNews (ref, GoodNews) news) (NF es)

To update definitions or modules, we call on |propagateNewsWithin|.

> propagateNews top news (NF (Right e :> es)) = do
>     news' <- propagateNewsWithin news e
>     propagateNews top news' (NF es)

Finally, if we encounter an older news bulletin when propagating news,
we can simply merge the two together.

> propagateNews top news (NF (Left oldNews :> es)) =
>   propagateNews top (mergeNews news oldNews) (NF es)


The |propagateNewsWithin| command will:
\begin{enumerate}
\item add the definition to the proof state without its children;
\item recursively propagate the news to the children, adding them as it goes;
\item call |tellCurrentEntry| to update the definition itself; and
\item move the focus out of the definition.
\end{enumerate}

> propagateNewsWithin :: NewsBulletin -> Entry NewsyFwd -> ProofState NewsBulletin
> propagateNewsWithin news e = do
>     -- Get current context and insert it as a layer
>     Dev es tip nsupply ss <- getAboveCursor
>     below <- getBelowCursor
>     putLayer (Layer es (mkCurrentEntry e) (reverseEntries below) tip nsupply ss)
>     -- Extract new information and make it the current location
>     let Just (Dev cs newTip newNSupply newSS) = entryDev e
>     putAboveCursor (Dev B0 newTip newNSupply newSS)
>     putBelowCursor F0
>     -- Propagate news through children and current entry
>     news'   <- propagateNews RecursivePropagate news cs
>     news''  <- tellCurrentEntry news'
>     -- Go out to where we were before
>     goOut
>     return news''


\subsection{Informing a current entry about its development}

\pierre{To be more carefully reviewed.}

The |tellEntry| function informs an entry about a news bulletin that
its development (if any) have already received. It applies the news
bulletin to the entry, returning the update entry together with
(potentially) more news.

\begin{danger}[Invariant: |tellEntry| on a definition]

If the entry is a definition, it must be the current entry of the
current cursor position (i.e. the entry should come from
|getLeaveCurrent|).

\end{danger}

\pierre{There is something fishy with this function and this
invariant. In reality, there are two function, one defined on
Parameters and called only on Parameters (in
@ProofState.Edition.Navigation@) (call it |tellParameterEntry|) and
one defined on Definitions and only called by itself and
|tellCurrentEntry| in a safe wrapper enforcing this invariant (call it
|tellDefinitionEntry|).

If we do the split, on one hand, the invariant will always be
enforced. On the other hand, we get two functions with a partial
pattern-matching. At least, with two explicitly named functions, one
can hardly ignore that one is for Parameters and the other for
Definitions.}

> tellEntry :: NewsBulletin -> Entry Bwd -> ProofState (NewsBulletin, Entry Bwd)

Modules carry no type information, so they are easy:

> tellEntry news (EModule n d) = return (news, EModule n d)

The update of a parameter consists in:
\begin{enumerate}
\item updating its type based on the news we received, and
\item adding to the news bulletin the fact that this parameter has
      been updated
\end{enumerate}

> tellEntry news (EPARAM (name := DECL :<: tv) sn k ty anchor) = do
>     let (ty' :=>: tv', n)  = tellNewsEval news (ty :=>: tv)
>     let ref = name := DECL :<: tv'
>     return (addNews (ref, n) news, EPARAM ref sn k ty' anchor)

To update a hole, we must first check to see if the news bulletin contains a
definition for it. If so, we fill in the definition (and do not need to
update the news bulletin). If not, we must  \pierre{why?}:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference; and
\item update the news bulletin with news about this definition.
\end{enumerate}
If the hole is |Hoping| and we have good news about its type, then we
restart elaboration to see if it can make any progress.

> tellEntry news (EDEF  ref@(name := HOLE h :<: tyv) sn
>                       dkind dev@(Dev {devTip=Unknown tt}) ty anchor)
>   | Just (ref'@(_ := DEFN tm :<: _), GoodNews) <- getNews news ref = do
>     -- We have a Definition for it
>     es   <- getInScope
>     tm'  <- bquoteHere (tm $$$ paramSpine es)
>     let  (tt', _) = tellNewsEval news tt
>          (ty', _) = tellNews news ty
>     -- Define the hole
>     return (news, EDEF ref' sn dkind (dev{devTip=Defined tm' tt'}) ty' anchor)
>
>   | otherwise = do
>     -- Not a Definition
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE h :<: tyv'
>          tip                  = case (min n n', h) of
>                                  (GoodNews, Hoping)  -> Suspended tt' ElabHope
>                                  _                   -> Unknown tt'
>     return  (addNews (ref, min n n') news,
>             EDEF ref sn dkind (dev{devTip=tip}) ty' anchor)

To update a hole with a suspended elaboration problem attached, we
proceed similarly to the previous case, but we also update the
elaboration problem.  If the news bulletin defines this hole, it had
better just be hoping for a solution \pierre{Is this an invariant we
are meant to enforce? Or something that might break one day? See bug
\#53.}, in which case we can safely ignore the attached |ElabHope|
process.

> tellEntry news (EDEF  ref@(name := HOLE h :<: tyv) sn
>                       dkind dev@(Dev {devTip=Suspended tt prob}) ty anchor)
>   | Just ne <- getNews news ref = do
>      -- We have a Definition for it
>      case prob of
>       ElabHope  -> do
>         -- The elaboration strategy \emph{has to} be to |Hope|
>         tellEntry news (EDEF ref sn dkind (dev{devTip=Unknown tt}) ty anchor)
>       _         -> do
>         -- \pierre{Is that a |throwError| or an |error|?}
>         throwError' . err . unlines $ [
>                     "tellEntry: news bulletin contains update", show ne,
>                     "for hole", show ref,
>                     "with suspended computation", show prob]
>   | otherwise = do
>     -- We don't have a Definition
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE h :<: tyv'
>          prob'                = tellEProb news prob
>          state                = if isUnstable prob' 
>                                   then SuspendUnstable 
>                                   else SuspendStable
>     suspendHierarchy state
>     return  (addNews (ref, min n n') news,
>             EDEF ref sn dkind (dev{devTip=Suspended tt' prob'}) ty' anchor)
>         where tellEProb :: NewsBulletin -> EProb -> EProb
>               tellEProb news = fmap (getLatest news)


To update a closed definition (|Defined|), we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference;
\item update the definition and re-evaluate it
         (\question{could this be made more efficient?}); and
\item update the news bulletin with news about this definition.
\end{enumerate}

> tellEntry news (EDEF  (name := DEFN tmL :<: tyv) sn dkind 
>                       dev@(Dev {devTip=Defined tm tt}) ty anchor) = do
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
>     return  (addNews (ref, GoodNews {-min (min n n') n''-}) news,
>             EDEF ref sn dkind (dev{devTip=Defined tm' tt'}) ty' anchor)


The |tellCurrentEntry| function informs the current entry about a news
bulletin that her children have already received, and returns the
updated news.

> tellCurrentEntry :: NewsBulletin -> ProofState NewsBulletin
> tellCurrentEntry news = do
>     e <- getLeaveCurrent
>     (news', e') <- tellEntry news e 
>     putEnterCurrent e'
>     return news'



When the current location or one of its children has suspended, we need to
update the outer layers.

> suspendHierarchy :: SuspendState -> ProofState ()
> suspendHierarchy ss = getLayers >>= putLayers . help ss
>   where
>     help :: SuspendState -> Bwd Layer -> Bwd Layer
>     help ss B0 = B0
>     help ss (ls :< l) = help ss' ls :< l{laySuspendState = ss'}
>       where ss' = min ss (laySuspendState l)