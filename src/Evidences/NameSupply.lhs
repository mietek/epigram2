\section{NameSupply}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, FlexibleInstances #-}

> module Evidences.NameSupply where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Reader

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.ErrorHandling

%endif

The |NameSupply| is the name generator used throughout Epigram. It is
inspired by the \emph{hierarchical names}~\cite{mcbride:free_variable}
used in Epigram the First. The aim of this structure is to
conveniently, provide unique free variable names.

A |NameSupply| is composed by a backward list of |(String, Int)| and an
|Int|. This corresponds to a hierarchical namespace and a free name in
that namespace. The structure of the namespace stack is justified as
follows. The |String| component provides name advice, which may not be
unique, while the |Int| uniquely identifies the namespace.

> type NameSupply = (Bwd (String, Int), Int)

Therefore, creating a fresh name in a given namespace simply consists
of incrementing the name counter:

> freshen :: NameSupply -> NameSupply
> freshen (sis, i) = (sis, i + 1)

Whereas creating a fresh namespace involves stacking up a new name
|s|, uniquely identified by |i|, and initializing the per-namespace
counter to |0|:

> freshNSpace :: NameSupply -> String -> NameSupply
> freshNSpace (sis, i) s = (sis :< (s,i), 0)

Intuitively, the function |name| computes a fresh name out of a given
name generator, decorating it with the human-readable label
|s|. Technically, |Name| is defined as
a list of |(String, Int)|. Hence, on that structure, the effect of
|trail| is to flatten the backward namespace into a (unique) |Name|.

> mkName :: NameSupply -> String -> Name
> mkName (sis, i) s = trail $ sis :< (s, i)




The |NameSupplier| type-class aims at giving the ability to use the
|NameSupply| in a safe way. There is trade-off here between ease of
implementation and safety. As it stands now, this version offers
moderate safety but is easy to use. Ideally, we would like most
of the code to use |NameSupplier| instead of manipulating the
|NameSupply| explicitly.

So, what does |NameSupplier| offer? 

> class (Applicative m, Monad m) => NameSupplier m where

First, |freshName| enables the safe creation of fresh names inside the
structure: it is provided with name advice and a \emph{body}. It calls
the body with a fresh name, while maintaining the coherency of the
namespace.

>     freshName :: String -> (Name -> m t) -> m t

Similarly, |forkNSupply| is a safe wrapper around |freshName| and
|freshNSpace|: |forkNSupply subname child dad| runs the |child| with
the current namespace extended with |subname|, then, |dad| gets the
result of |child|'s work and can go ahead with a fresh variable index.

>     forkNSupply  :: String -> m s -> (s -> m t) -> m t

Finally, we have an |askNSupply| operation, to \emph{read} the current
|NameSupply|. This was a difficult choice: we give up the read-only
access to the |NameSupply|, allowing the code to use it in potentially
nasty ways. This operation has been motivated by |equal| that calls
into |exQuote|. |exQuote| on a paramater uses and abuses some
invariants of the name fabric, hence needs direct access to the
|NameSupply| structure.

>     askNSupply   :: m NameSupply

Because of the presence of |askNSupply|, we have here a kind of Reader
monad on steroids. This might not be true forever; we can hope to replace
|askNSupply| by a finer grained mechanism.


Sometimes you want a fresh value rather than a reference:

< fresh :: NameSupplier m => (String :<: TY) -> (VAL -> m t) -> m t
< fresh xty f = freshRef xty (f . pval)



\subsection{|(->) NameSupply| is a |NameSupplier|}

To illustrate the implementation of a |NameSupplier|, we implement the
|NameSupply| Reader monad:

> instance NameSupplier ((->) NameSupply) where
>     freshName x f r = f (mkName r x) (freshen r)
>     forkNSupply s child dad nsupply = (dad . child) (freshNSpace nsupply s) (freshen nsupply)
>     askNSupply r = r



\subsection{|ReaderT NameSupply| is a |NameSupplier|}

Once we have a |NameSupplier| for the |NameSupply| Reader monad, we
can actually get it for any |ReaderT NameSupply|. This is as simple
as:

> instance (Monad m, Applicative m) => NameSupplier (ReaderT NameSupply m) where
>     freshName st body = do
>         nsupply <- ask
>         lift $ freshName st (runReaderT . body) nsupply
>     forkNSupply s child dad = do
>         c <- local (flip freshNSpace s) child
>         d <- local freshen (dad c)
>         return d
>     askNSupply = ask

\subsection{The |Fresh| monad is a |NameSupplier|}
\label{subsec:Evidences.NameSupplier.fresh-monad}

One such example is the |Fresh| monad:

> type Fresh = ReaderT NameSupply (Either StackError)

That is, a Reader of |NameSupply| on top of an Error of
|StackError|. Running a type-checking process is therefore a simple
|runReader| operation:

> runFresh :: Fresh a -> NameSupply -> Either StackError a
> runFresh = runReaderT

