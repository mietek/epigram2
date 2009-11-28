\section{Missing Library}

%if False

> module MissingLibrary where

> import Control.Applicative
> import Data.Foldable
> import Data.Monoid

%endif

> class Functor f => HalfZip f where
>   halfZip :: f x -> f y -> Maybe (f (x,y))

> class Monad m => MonadTrace m where
>     traceErr :: String -> m a

> instance MonadTrace Maybe where
>     traceErr _ = Nothing

%if False

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

%endif

> ffilter :: (Foldable f, Alternative a, Monoid (a x)) => (x -> Bool) -> f x -> a x
> ffilter p = foldMap (\x -> if p x then pure x else empty)