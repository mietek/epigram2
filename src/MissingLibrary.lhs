> module MissingLibrary where

> class Functor f => HalfZip f where
>   halfZip :: f x -> f y -> Maybe (f (x,y))
>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

