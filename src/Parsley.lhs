\section{Parsley}

Here is a bargain basement parser combinator library. It does
nothing fancy, except that it makes it easy to recover the text
block that gave rise to a term. It is hopelessly inefficient,
but we can spend more effort when it becomes a more serious
problem. In particular, we can easily represent extents
numerically.

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module Parsley where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State

%endif

> newtype P t x = P {runP :: [t] -> Maybe ([t], x, [t])}
>
> parse :: P t x -> [t] -> Maybe x
> parse p ts = case runP p ts of
>   Just (_, x, []) -> Just x
>   _ -> Nothing

It's a |Monad| and all that.

> instance Monad (P t) where
>   return x = P $ \ ts -> Just ([], x, ts)
>   P s >>= f = P $ \ts -> do
>     (sts, s', ts)  <- s ts
>     (tts, t', ts)  <- runP (f s') ts
>     return (sts ++ tts, t', ts)
>
> instance Functor (P t) where
>   fmap = ap . return
>
> instance Applicative (P t) where
>   pure   = return
>   (<*>)  = ap
>
> instance Alternative (P t) where
>   empty = P $ \ _ -> Nothing
>   p <|> q = P $ \ ts -> runP p ts <|> runP q ts
>
> instance MonadPlus (P t) where
>   mzero  = empty
>   mplus  = (<|>)

You can consume the next thing.

> next :: P t t
> next = P $ \ ts -> case ts of
>   []        -> Nothing
>   (t : ts)  -> Just ([t], t, ts)

You can consume everything!

> pRest :: P t [t]
> pRest = P $ \ ts -> Just (ts, ts, [])

You can peek ahead, perhaps to check you've finished.

> peek :: P t [t]
> peek = P $ \ ts -> Just ([], ts, ts)
>
> pEnd :: P t ()
> pEnd = guard =<< (|null peek|)

You can make a parser give you the input extent it consumes as well as
its output.

> pExt :: P t x -> P t ([t], x)
> pExt (P x) = P $ \ ts -> do
>   (xts, x', ts) <- x ts
>   return (xts, (xts, x'), ts)

Parsing separated sequences:

> pSep :: P t s -> P t x -> P t [x]
> pSep s p = (:) <$> p <*> many (s *> p) <|> pure []

Post-processing parser output:

> grok :: (a -> Maybe b) -> P t a -> P t b
> grok f p = do
>   a <- p
>   case f a of
>     Just b -> return b
>     Nothing -> empty
>
> ok :: (a -> Bool) -> a -> Maybe a
> ok p a = (|a {guard (p a)}|)

Token-checking:

> tok :: (t -> Bool) -> P t t
> tok p = grok (ok p) next
>
> teq :: Eq t => t -> P t ()
> teq t = tok (== t) *> pure ()
