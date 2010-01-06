\section{Rooty}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables,
>     MultiParamTypeClasses #-}

> module Rooty where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Data.Maybe

> import BwdFwd
> import Root
> import Tm
> import MissingLibrary

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


As an other example, here is a monad which always provide your binders
with a fresh reference. It starts as usual, with a |ReaderT Root|
enclosing the |Maybe| monad. The motivation for the |Maybe| comes from
its use in |opTy|, which asks for a |MonadTrace|.

> data Fresh a = Fresh { inFresh :: Root -> Maybe a }

This will, obviously, run the following way:

> runFresh :: Root -> Fresh a -> a
> runFresh root f = fromJust $ inFresh f root

The instanciation of Rooty here is quite standard, actually relying on
the Rootyness of |(->) Root|. 

> instance Rooty Fresh where
>     freshRef st f = Fresh $ Rooty.freshRef st (inFresh . f)
>     forkRoot s child dad = Fresh $ \root -> do
>                            c <- inFresh child (room root s)
>                            d <- inFresh (dad c) (roos root)
>                            return d
>     root = Fresh $ Just

The Monad instance is particular (hence preventing the use of |ReaderT
Root|) in that it's not really a reader: going through each binder, we
extend the namespace. Hence, each |freshRef| in subsequent bindings
will be really fresh.

> instance Monad Fresh where
>     return x = Fresh $ const $ Just x
>     x >>= g = Fresh $ \r -> do
>               a <- inFresh x r
>               inFresh (g a) (room r "z")

Then comes the usual junk, |Functor|, |Applicative|, and a fake
|MonadError|.

> instance Functor Fresh where
>     fmap f (Fresh g) = Fresh $ (fmap f) . g 
>
> instance Applicative Fresh where
>     pure = return
>     (<*>) = ap
>
> instance MonadError [String] Fresh  where
>     throwError _ = Fresh $ const Nothing
>     catchError = error "Fresh has no catchError"



> data Check a = Check { inCheck :: Root -> Either [String] a }
>
> typeCheck :: Root -> Check a -> a
> typeCheck root f = case inCheck f root of
>                     Left x -> error $ "typeCheck: " ++ (head x)
>                     Right l -> l
>
> instance Rooty Check where
>     freshRef st f = Check $ Rooty.freshRef st (inCheck . f)
>     forkRoot s child dad = Check $ \root -> do
>                            c <- inCheck child (room root s)
>                            d <- inCheck (dad c) (roos root)
>                            return d
>     root = Check $ Right
>
> instance Monad Check where
>     return x = Check $ const $ Right x
>     x >>= g = Check $ \r -> do
>               a <- inCheck x r
>               inCheck (g a) r
>
> instance Functor Check where
>     fmap f (Check g) = Check $ (fmap f) . g 
>
> instance Applicative Check where
>     pure = return
>     (<*>) = ap
>
> instance MonadPlus Check where
>     mzero = throwError ["empty"]
>     x `mplus` y = Check $ \r -> inCheck x r `mplus` inCheck y r

> instance Alternative Check where
>     empty = mzero
>     (<|>) = mplus

> instance MonadError [String] Check  where
>     throwError s = Check $ const $ Left s
>     catchError = error "Check has no catchError"
