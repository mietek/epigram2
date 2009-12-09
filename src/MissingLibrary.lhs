\section{Missing Library}

%if False

> {-# LANGUAGE FlexibleInstances #-}

> module MissingLibrary where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error (Error, strMsg)
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

> instance Error e => MonadTrace (Either e) where
>     traceErr s = Left (strMsg s)

> newtype I x = I {unI :: x} deriving (Show, Eq)
> instance Functor I where
>   fmap f (I s) = I (f s)
> instance Applicative I where
>   pure         = I
>   I f <*> I s  = I (f s)

> instance Error [String] where
>   strMsg s = [s]

> instance Error x => Applicative (Either x) where
>   pure = return
>   (<*>) = ap

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap


> eitherRight :: Either a b -> Maybe b
> eitherRight (Right x)  = Just x
> eitherRight (Left _)   = Nothing

> catchMaybe :: MonadTrace m => Maybe a -> String -> m a
> catchMaybe (Just x) _ = return x
> catchMaybe Nothing s = traceErr s

%if False

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

%endif