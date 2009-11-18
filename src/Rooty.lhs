\section{Rooty}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Rooty where

> import Control.Applicative

> import BwdFwd
> import Root
> import Tm

%endif

The |Rooty| type-class aims at giving the ability to some structures
to use the Root in a safe way. There is trade-off here, between ease
of implementation and safety. As it stands now, this version offers a
moderate safety but is easy to use, by having not required a lot of
changes in the code base. Ideally, we would like that most of the code
uses |Rooty| instead of manipulating the Root explicitly.

So, what does |Rooty| offer? First, |freshRef| enables the safe
creation of fresh names inside the structure: it is provided with an
informative name, the variable type, and a \emph{body} consuming that
free variable. It returns the body with the free variable filled in,
while maintaining the coherency of the namespace.

Similarly, |forkRoot| is a safe wrapper around |room| and |roos|:
|forkRoot subname child dad| runs the |child| with the current
namespace extended with |subname|. Then, |dad| gets the result of
|child|'s work and can go ahead with a fresh variable index.

Finally, we have a |root| operation, to \emph{read} the current
Root. This was a difficult choice: we give up the read-only access to
the Root, allowing the code to use it in potentially nasty ways. This
operation has been motivated by |equal| that calls into
|exQuote|. |exQuote| on a paramater uses and abuses some invariants of
the name fabric, hence needs direct access to the |Root| structure.

Because of the presence of |root|, we have here a kind of Reader monad
on steroid. This might be true forever, we can hope to replace |root|
by a finer grained mechanism.

> class (Applicative m, Monad m) => Rooty m where
>     freshRef :: (String :<: TY) -> (REF -> m t) -> m t
>     forkRoot :: String -> m s -> (s -> m t) -> m t
>     root :: m Root

To illustrate the implementation of |Rooty|, we implement on the
|Root| Reader monad. |freshRef| is straightforward, by the code in
@Root.lhs@. |forkRoot| directly follows from its specification. |root|
is trivial as well.

> instance Rooty ((->) Root) where
>     freshRef = Root.freshRef
>     forkRoot s child dad root = (dad . child) (room root s) (roos root)
>     root r = r