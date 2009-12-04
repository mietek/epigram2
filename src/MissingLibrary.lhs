\section{Missing Library}

%if False

> module MissingLibrary where

> import Control.Monad
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


> newtype I x = I {unI :: x} deriving (Show, Eq)
> instance Functor I where
>   fmap f (I s) = I (f s)
> instance Applicative I where
>   pure         = I
>   I f <*> I s  = I (f s)

> instance Applicative (Either x) where
>   pure = return
>   (<*>) = ap
> instance Monad (Either e) where
>     return = Right
>     x >>= f = either Left f x


> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap


> eitherRight :: Either a b -> Maybe b
> eitherRight (Right x)  = Just x
> eitherRight (Left _)   = Nothing

%if False

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

%endif