\section{Navigating in the Proof Context}
\label{sec:Proofstate.Edition.Navigation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.Navigation where

> import Control.Applicative

> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import ProofState.Edition.ProofContext
> import ProofState.Edition.Entries
> import ProofState.Edition.News
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import {-# SOURCE #-} Elaboration.Wire

> import Evidences.Tm

%endif


In Section~\ref{sec:ProofState.Structure.Developments}, we have
developed the notion of |Development|, a tree reifing the proof
construction process. In order to navigate this tree, we have computed
its zipper in Section~\ref{sec:ProofState.Edition.ProofContext}, the
|ProofContext|. At this stage, we have a notion of \emph{movement} in
the proof context.

However, we had to postpone the development of navigation commands to
this stage, where we have the ability to \emph{edit} the |ProofState|
(Section~\ref{sec:ProofState.Edition.ProofState}). Indeed, when moving
down, we might hit a news bulletin. A news bulletin is a lazy edition
process. In order to move, we have to propogate the news, hence
effectively editing the proof state.



\subsection{One-step navigation}


We shall now develop this navigation kit, comfortably installed in the
|ProofState| monad. First, some vocabulary. The \emph{focus} is the
current development; it contains a \emph{cursor} which is the point at
which changes take place. Consider the following development presented
in Figure~\ref{fig:ProofState.Edition.Navigation.devpmt}: we have that
the development |B| is in focus, with |y| above the cursor and |z|
below it.

\begin{figure}

{\include{ProofState/Edition/NavigationExamples}}

\caption{Navigation in a development}
\label{fig:ProofState.Edition.Navigation.devpmt}
\end{figure}


The navigation commands are the following:

\begin{itemize}

\item Current entry navigation:

\begin{itemize}
\item |putEnterCurrent|
\item |leaveEnterCurrent|
\end{itemize}

\item Cursor navigation:

\begin{itemize}
\item |cursorUp| moves the cursor up by one entry (under |E| in the example);
\item |cursorDown| moves the cursor down by one entry (under |z| in
      the example);
\end{itemize}

\item Focus navigation:

\begin{itemize}
\item |goIn| moves the focus in the first definition above the cursor,
      and brings the cursor at the bottom of the newly focused development
      (inside |E| and below |b| in the example);
\item |goOut| moves the focus out to the development that contains it, with
      the cursor at the bottom of the development (under |G| in the example);
\item |goOutBelow| moves the focus out to the development that contains
      it, with the cursor under the previously focused entry
      (under |B| in the example);
\item |goUp| moves the focus up to the closest definition and leaves the
      cursor at the bottom (inside |A| in the example); and
\item |goDown| moves the focus down to the closest definition and leaves
      the cursor at the bottom (inside |C| in the example).
\end{itemize}
\end{itemize}

These commands fail with an error if they are impossible because the
proof context is not in the required form. Things are slightly more complicated
than the above description because of the possibility of news bulletins below
the cursor; as these are propagated lazily, they must be pushed down when the
cursor or focus move.

\subsubsection{From Entry to Current entry, and back}

With |getCurrentEntry| and |putCurrentEntry|, we know how to access
the current entry, and overwrite it. However, when navigating through
the proof context, we will change focus, therefore \emph{leaving} the
current entry, or \emph{entering} into another. 

When leaving the current entry, the current entry is turned back into
a conventional entry, so that it can inserted with its peers in the
development (above or below). In a word, this operation \emph{zip}
back the current entry.

> getLeaveCurrent :: ProofState (Entry Bwd)
> getLeaveCurrent = do
>     currentEntry <- getCurrentEntry
>     Dev above tip root state <- getAboveCursor
>     below <- getBelowCursor
>     let dev = Dev (above <>< below) tip root state
>     case currentEntry of
>         CDefinition dkind ref xn ty a  ->  return $ EDEF ref xn dkind dev ty a
>         CModule n                      ->  return $ EModule n dev

Conversely, when entering a new development, the former entry needs to
be \emph{unzipped} to form the current development. 

> putEnterCurrent :: Entry Bwd -> ProofState ()
> putEnterCurrent (EDEF ref xn dkind dev ty a) = do
>     l <- getLayer
>     replaceLayer $ l { currentEntry = CDefinition dkind ref xn ty a}
>     putAboveCursor dev
> putEnterCurrent (EModule [] dev) = putAboveCursor dev
> putEnterCurrent (EModule n dev) = do
>     l <- getLayer
>     replaceLayer $ l { currentEntry = CModule n }
>     putAboveCursor dev


\subsubsection{Cursor navigation}

Cursor movement is straightforward, as there is no news to worry
about. We simply move an entry above the cursor to one below, or vice
versa.


> cursorUp :: ProofState ()
> cursorUp = do
>     -- Look above
>     above <- getEntriesAbove
>     case above of
>         aboveE :< e -> do
>             below <- getBelowCursor
>             -- Move |e| from |above| to |below|
>             putEntriesAbove aboveE
>             putBelowCursor $ e :> below
>             return ()
>         B0 -> do
>             -- There is no above..
>             throwError' $ err "cursorUp: cannot move cursor up."
>
> cursorDown :: ProofState ()
> cursorDown = do
>     -- Look below
>     above <- getEntriesAbove
>     below <- getBelowCursor
>     case below of
>         e :> belowE -> do
>             -- Move |e| from |below| to |above|
>             putEntriesAbove (above :< e)
>             putBelowCursor belowE
>             return ()
>         F0 -> do
>             -- There is no below..
>             throwError' $ err "cursorDown: cannot move cursor down."

\subsubsection{Focus navigation}


\pierre{I'm somewhat uneasy with this kind of definition. On one hand,
it is thriving to avoid failure (looking up for an actual definition,
then moving into it). On the other hand, it is doing two things,
non-compositionally. However, writing two distinct functions --- one
doing the lookup, the other moving in a definition --- exposes some
invariants ("called on a definition" for the second one) that I don't
know how to enforce with types instead of dynamic checks.}


The |goIn| command moves the cursor upward, until it reaches a
definition. If one can be found, it enters it and goes at the bottom.

> goIn :: ProofState ()
> goIn = do
>     above <- getEntriesAbove
>     case above of
>         B0 -> do
>           -- Nothing above: we cannot go above
>           throwError' $ err "goIn: you can't go that way."
>         aboveE :< e -> case entryDev e of
>           Nothing   -> do
>              -- This entry is not a Definition: look further up
>              cursorUp >> goIn
>           Just dev  -> do
>              -- We are right into a Definition
>              oldFocus  <- getAboveCursor
>              below  <- getBelowCursor
>              -- Set the focus to this Definition
>              putLayer $ Layer  {  aboveEntries = aboveE
>                                ,  currentEntry = mkCurrentEntry e
>                                ,  belowEntries = reverseEntries below
>                                ,  layTip = devTip oldFocus
>                                ,  layNSupply = devNSupply oldFocus
>                                ,  laySuspendState = devSuspendState oldFocus }
>              -- Set cursor at the bottom
>              putAboveCursor dev
>              putBelowCursor F0
>              return ()


The |goOut| command moves the focus to the outer layer, with the
cursor at the bottom of it. Therefore, we zip back the current
development, with the additional burden of dealing with news.

> goOut :: ProofState ()
> goOut = do
>     -- Leave the current entry
>     e <- getLeaveCurrent
>     -- Move one layer out
>     mLayer <- optional removeLayer
>     case mLayer of
>         Just l -> do 
>             -- Update the current development
>             putAboveCursor $ Dev  {  devEntries       =  aboveEntries l :< e
>                                   ,  devTip           =  layTip l
>                                   ,  devNSupply       =  layNSupply l
>                                   ,  devSuspendState  =  laySuspendState l }
>             putBelowCursor F0
>             propagateNews NormalPropagate [] (belowEntries l)
>             -- Here, the cursor is at the bottom of the current development
>             return ()
>         Nothing -> do
>             -- Already at outermost position
>             throwError' $ err "goOut: you can't go that way."



The |goOutBelow| variant has a similar effect than |goOut|, excepted
that it brings the cursor right under the previous point of focus.

> goOutBelow :: ProofState ()
> goOutBelow = do
>     -- Retrieve the number of entries below the previous point of focus
>     ls <- getLayers
>     case ls of
>         _ :< Layer{belowEntries=below} -> do
>             -- Go out: end up at the bottom of the development
>             goOut
>             -- Move cursor up by as many entries there was
>             Data.Traversable.mapM (const cursorUp) below
>             return ()
>         B0 -> throwError' $ err "goOutBelow: you can't go that way."



The |goUp| command moves the focus upward, looking for a
definition. If one can be found, the cursor is moved at the bottom of
the new development.

> goUp :: ProofState ()
> goUp = goUpAcc (NF F0)
>   where
>     goUpAcc :: NewsyEntries -> ProofState ()
>     goUpAcc (NF visitedBelow) = do
>         -- Get the directly enclosing layer
>         l <- getLayer
>         case l of
>           (Layer (aboveE :< e) m (NF below) tip nsupply state) -> 
>             -- It has at least one entry
>             case entryDev e of
>             Just dev -> do
>                 -- The entry is a Definition
>                 
>                 -- Leave our current position
>                 currentE <- getLeaveCurrent
>                 -- Put the cursor at the bottom of the development
>                 putAboveCursor dev
>                 putBelowCursor F0
>                 -- Set focus on this definition
>                 let belowE = NF  $    visitedBelow 
>                                  <+>  (Right (reverseEntry currentE) :> below)
>                 replaceLayer $ l  {  aboveEntries  =  aboveE
>                                   ,  currentEntry  =  mkCurrentEntry e
>                                   ,  belowEntries  =  belowE}
>                 return ()
>             Nothing -> do
>                 -- The entry is a Parameter
>
>                 -- Move up, accumulating the the current entry
>                 replaceLayer $ l { aboveEntries = aboveE }
>                 goUpAcc $ NF (Right (reverseEntry e) :> visitedBelow)
>           _ -> do
>             -- There is no up
>             throwError' $ err "goUp: you can't go that way."


Similarly to |goUp|, the |goDown| command moves the focus downward,
looking for a definition. If one can be found, the cursor is placed at
the bottom of the new development. As often, moving down implies
dealing with news: we accumulate them as we go, updating the
parameteres on our way.

> goDown :: ProofState ()
> goDown = goDownAcc B0 []
>   where
>     goDownAcc :: Entries -> NewsBulletin -> ProofState ()
>     goDownAcc visitedAbove visitedNews = do
>         -- Get the directly enclosing layer
>         l <- getLayer
>         case l of
>           (Layer {aboveEntries = above , belowEntries=NF (ne :> belowNE)}) -> 
>             -- What is the entry below?
>             case ne of
>             Left newsBulletin -> do 
>                 -- A news bulletin:
>
>                 -- Keep going down, accumulating the news
>                 replaceLayer $ l { belowEntries = NF belowNE }
>                 goDownAcc visitedAbove $ mergeNews visitedNews newsBulletin
>             Right e -> 
>                 -- A real entry:
>                 
>                 -- Definition or Parameter?
>                 case entryCoerce e of
>                 Left (Dev es' tip' nsupply' ss') -> do
>                   -- Definition:
>                    
>                   -- Leave our current position
>                   currentE <- getLeaveCurrent
>                   -- Set focus on this definition
>                   let aboveE = (above :< currentE) <+> visitedAbove
>                   replaceLayer $ l  {  aboveEntries  =  aboveE
>                                     ,  currentEntry  =  mkCurrentEntry e
>                                     ,  belowEntries  =  NF belowNE }
>                   -- Put the cursor at the bottom of the development
>                   -- The suspend state is cleared because there are no
>                   -- entries in the |Dev|; the state will be updated
>                   -- during news propagation.
>                   putAboveCursor (Dev B0 tip' nsupply' SuspendNone)
>                   putBelowCursor F0
>                   -- Push the collected news from above into the entries
>                   propagateNews NormalPropagate visitedNews es'
>                   return ()
>                 Right param -> do
>                   -- Parameter:
>
>                   -- Push the news into it
>                   (news, param') <- tellEntry visitedNews param
>                   -- Keep going down
>                   replaceLayer  $ l { belowEntries = NF belowNE }
>                   goDownAcc (visitedAbove :< param') news
>           _ -> do
>             -- There is no down
>             throwError' $ err "goDown: you can't go that way."



\subsection{Many-step Navigation}


The following functions are trivial iterations of the ones developed
above. 

> cursorTop :: ProofState ()
> cursorTop = much cursorUp
>
> cursorBottom :: ProofState ()
> cursorBottom = much cursorDown
>
> goTop :: ProofState ()
> goTop = much goUp
>
> goBottom :: ProofState ()
> goBottom = much goDown
>
> goRoot :: ProofState ()
> goRoot = much goOut
