> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE PatternGuards, FlexibleInstances, TypeOperators,
>     DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

> module SourceLang.Parx where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable
> import Data.Foldable

> newtype Parx t x = Parx {parx :: [t] -> ([t], Maybe x, [t])}

> instance Monad (Parx t) where
>   return x = Parx $ \ ts -> ([], Just x, ts)
>   Parx f >>= g = Parx $ \ ts -> case f ts of
>     (us, Just x, vs) -> case parx (g x) vs of
>       (ws, my, xs) -> (us ++ ws, my, xs)
>     (us, Nothing, vs) -> (us, Nothing, vs)

> instance MonadPlus (Parx t) where
>   mzero = Parx $ \ ts -> ([], Nothing, ts)
>   mplus (Parx f) (Parx g) = Parx $ \ ts -> case (f ts, g ts) of
>     (r@(_, Just _, _), _) -> r
>     (_, r@(_, Just _, _)) -> r
>     (l@(us, _, _), r@(vs, _, _))
>       | length us >= length vs  -> l
>       | otherwise               -> r

> like :: (t -> Maybe x) -> Parx t x
> like f = Parx $ \ ts -> case ts of
>   (t : ts) | Just x <- f t -> ([t], Just x, ts)
>   _ -> ([], Nothing, ts)

> tok :: (t -> Bool) -> Parx t t
> tok p = like $ \ t -> (|t (-guard (p t)-)|)

> teq :: Eq t => t -> Parx t ()
> teq t = (|() (-tok (t ==)-)|)

> done :: Parx t ()
> done = Parx $ \ ts -> case ts of
>   [] -> ([], Just (), [])
>   _ -> ([], Nothing, ts)

> data t :~ x = [t] :~ x deriving (Functor, Foldable, Traversable, Show)

> source :: Parx t x -> Parx t (t :~ x)
> source p = Parx $ \ ts -> case parx p ts of
>   (us, Just x, vs) -> (us, Just (us :~ x), vs)
>   (us, Nothing, vs) -> (us, Nothing, vs)

> class Gappy t where
>   gap :: Parx t ()

> gmany :: Gappy t => Parx t x -> Parx t [x]
> gmany p = (|id (-gap-) (many (|id p (-gap-)|))|)

> pad :: Gappy t => Parx t x -> Parx t x
> pad p = (|id (-gap-) p (-gap-)|)

> punc :: (Gappy t, Eq t) => t -> Parx t ()
> punc t = pad (teq t)

> upto :: Parx t () -> Parx t [t]
> upto p = (|[] (-p-) | like Just : upto p|)

> precook :: Parx t [s] -> Parx s x -> Parx t x
> precook p q = p >>= \ ss -> case parx q ss of
>   (_, Just x, []) -> (|x|)
>   _ -> (|)
