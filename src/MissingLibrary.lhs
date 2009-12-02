\section{Missing Library}

%if False

> module MissingLibrary where

> import Control.Applicative
> import Control.Monad.State
> import Data.Foldable
> import Data.Monoid

%endif

> class Functor f => HalfZip f where
>   halfZip :: f x -> f y -> Maybe (f (x,y))

> class Monad m => MonadTrace m where
>     traceErr :: String -> m a

> instance MonadTrace Maybe where
>     traceErr _ = Nothing

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap

%if False

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

%endif