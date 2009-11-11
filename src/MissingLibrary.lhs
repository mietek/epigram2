\section{Missing Library}

%if False

> module MissingLibrary where

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