\section{BwdFwd}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module BwdFwd where

> import Data.Monoid
> import Data.Foldable
> import Data.Traversable
> import Control.Applicative

%endif

%format :< = ":\!<"
%format :> = ":\!>"
%format <+> = "\oplus"

Backward and forward lists, applicative with zipping.

> data Bwd x = B0 | Bwd x :< x
> data Fwd x = F0 | x :> Fwd x

> instance Applicative Bwd where
>   pure x                     = pure x       :< x
>   (fs :< f)  <*>  (ss :< s)  = (fs <*> ss)  :< f s
>   _          <*>  _          = B0
>
> instance Applicative Fwd where
>   pure x                     = x    :>  pure x
>   (f :> fs)  <*>  (s :> ss)  = f s  :>  (fs <*> ss)
>   _          <*>  _          = F0

> instance Monoid (Bwd x) where
>   mempty = B0
>   mappend xs B0          = xs
>   mappend xs (ys :< y)  = mappend xs ys :< y
>
> instance Monoid (Fwd x) where
>   mempty = F0
>   mappend F0         ys  = ys
>   mappend (x :> xs)  ys  = x :> mappend xs ys

> trail :: (Applicative f, Foldable t, Monoid (f a)) => t a -> f a
> trail = foldMap pure

> (<+>) :: Monoid x => x -> x -> x
> (<+>) = mappend

%if False

> instance Traversable Bwd where
>   traverse f B0         = (|B0|)
>   traverse f (xs :< x)  = (|traverse f xs :< f x|)
>
> instance Functor Bwd where
>   fmap = fmapDefault
>
> instance Foldable Bwd where
>   foldMap = foldMapDefault
>
> instance Traversable Fwd where
>   traverse f F0         = (|F0|)
>   traverse f (x :> xs)  = (|f x :> traverse f xs|)
>
> instance Functor Fwd where
>   fmap = fmapDefault
>
> instance Foldable Fwd where
>   foldMap = foldMapDefault

%endif
