\section{Generic name supplier}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables,
>     MultiParamTypeClasses #-}

> module NameSupply.NameSupplier where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Reader

> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import Evidences.Tm


%endif

The |NameSupplier| type-class aims at giving the ability to some
structures to use the |NameSupply| in a safe way. There is trade-off
here, between ease of implementation and safety. As it stands now,
this version offers a moderate safety but is easy to use, by having
not required a lot of changes in the code base. Ideally, we would like
that most of the code uses |NameSupplier| instead of manipulating the
|NameSupply| explicitly.

So, what does |NameSupplier| offer? First, |freshRef| enables the safe
creation of fresh names inside the structure: it is provided with an
informative name, the variable type, and a \emph{body} consuming that
free variable. It returns the body with the free variable filled in,
while maintaining the coherency of the namespace.

Similarly, |forkNSupply| is a safe wrapper around |freshName| and
|freshNSpace|: |forkNSupply subname child dad| runs the |child| with
the current namespace extended with |subname|. Then, |dad| gets the
result of |child|'s work and can go ahead with a fresh variable index.

Finally, we have a |askNSupply| operation, to \emph{read} the current
|NameSupply|. This was a difficult choice: we give up the read-only
access to the |NameSupply|, allowing the code to use it in potentially
nasty ways. This operation has been motivated by |equal| that calls
into |exQuote|. |exQuote| on a paramater uses and abuses some
invariants of the name fabric, hence needs direct access to the
|NameSupply| structure.

Because of the presence of |askNSupply|, we have here a kind of Reader
monad on steroid. This might be true forever, we can hope to replace
|askNSupply| by a finer grained mechanism.

> class (Applicative m, Monad m) => NameSupplier m where
>     freshRef    :: (String :<: TY) -> (REF -> m t) -> m t
>     forkNSupply  :: String -> m s -> (s -> m t) -> m t
>     askNSupply   :: m NameSupply

Sometimes you want a fresh value rather than a reference:

> fresh :: NameSupplier m => (String :<: TY) -> (VAL -> m t) -> m t
> fresh xty f = freshRef xty (f . pval)


\subsection{|(->) NameSupply| is a |NameSupplier|}

To illustrate the implementation of a |NameSupplier|, we implement the
|NameSupply| Reader monad:

> instance NameSupplier ((->) NameSupply) where
>     freshRef (x :<: ty) f r = f (mkName r x := DECL :<: ty) (freshName r)
>     forkNSupply s child dad nsupply = (dad . child) (freshNSpace nsupply s) (freshName nsupply)
>     askNSupply r = r


\subsection{|ReaderT NameSupply| is a |NameSupplier|}

Once we have a |NameSupplier| for the |NameSupply| Reader monad, we
can actually get it for any |ReaderT NameSupply|. This is as simple
as:

> instance (Monad m, Applicative m) => NameSupplier (ReaderT NameSupply m) where
>     freshRef st body = do
>         nsupply <- ask
>         lift $ freshRef st (runReaderT . body) nsupply
>     forkNSupply s child dad = do
>         c <- local (flip freshNSpace s) child
>         d <- local freshName (dad c)
>         return d
>     askNSupply = ask

\subsection{|NameSupply -> Either StackError a| is a |NameSupplier|}

One such example is the |Check| monad:

> type Check = ReaderT NameSupply (Either StackError)

That is, a Reader of |NameSupply| on top of an Error of
|StackError|. Running a type-checking process is therefore is simple
|runReader| operation:

> typeCheck :: Check a -> NameSupply -> Either StackError a
> typeCheck = runReaderT

