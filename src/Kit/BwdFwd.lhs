\section{BwdFwd}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE  TypeOperators, TypeSynonymInstances, TypeFamilies,
>               FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

> module Kit.BwdFwd where

> import Data.Monoid
> import Data.Foldable hiding (foldl, foldr)
> import Data.Traversable
> import Control.Applicative

> import Kit.MissingLibrary

%endif

%format :< = ":\!<"
%format :> = ":\!>"
%format <+> = "\oplus"

Backward and forward lists, applicative with zipping.

> data Bwd x = B0 | Bwd x :< x deriving (Show, Eq)
> infixl 5 :<
> data Fwd x = F0 | x :> Fwd x deriving (Show, Eq)
> infixr 5 :>

> bwdList :: [x] -> Bwd x
> bwdList = foldl (:<) B0
> fwdList :: [x] -> Fwd x
> fwdList = foldr (:>) F0

> (<><) :: Bwd x -> Fwd x -> Bwd x
> infixl 5 <><
> xs <>< F0 = xs
> xs <>< (y :> ys) = (xs :< y) <>< ys

> (<>>) :: Bwd x -> Fwd x -> Fwd x
> infixl 5 <>>
> B0 <>> ys = ys
> (xs :< x) <>> ys = xs <>> (x :> ys)

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

> instance Alternative Bwd where
>   empty = mempty
>   (<|>) = mappend

> instance Monoid (Fwd x) where
>   mempty = F0
>   mappend F0         ys  = ys
>   mappend (x :> xs)  ys  = x :> mappend xs ys

> class Applicative f => Naperian f where
>   type Log f
>   (!.) :: f x -> Log f -> Maybe x
>   logTable :: f (Log f)

> instance Naperian Bwd where -- cheeky!
>   type Log Bwd = Int
>   (xs :< x)  !. 0  = Just x
>   (xs :< x)  !. i  = xs !. (i - 1)
>   _          !. _  = Nothing
>   logTable = (1 + logTable) :< 0

> bwdLength :: Bwd x -> Int
> bwdLength = getSum . foldMap (\_ -> Sum 1)

> bwdNull :: Bwd x -> Bool
> bwdNull B0        = True
> bwdNull (_ :< _)  = False

> bwdFoldCtxt :: (Fwd x -> t) ->
>                (t -> x -> Fwd x -> t) ->
>                Bwd x -> t
> bwdFoldCtxt n s xs = help xs F0 
>     where help B0 ys = n ys
>           help (xs :< x) ys = s (help xs (x :> ys)) x ys

> elemIndex :: Eq x => x -> Bwd x -> Maybe Int
> elemIndex x = bwdFoldCtxt (\_ -> Nothing)
>                            (\t y i -> 
>                             if y == x then 
>                                 Just $ sum i 
>                             else 
>                                 t)
>     where sum = foldr' (\_ x -> x+1) 0



%if False

> instance Traversable Bwd where
>   traverse f B0         = (|B0|)
>   traverse f (xs :< x)  = (|(f ^$ xs) :< f x|)
>
> instance Functor Bwd where
>   fmap = fmapDefault
>
> instance Foldable Bwd where
>   foldMap = foldMapDefault
>
> instance Traversable Fwd where
>   traverse f F0         = (|F0|)
>   traverse f (x :> xs)  = (|f x :> (f ^$ xs)|)
>
> instance Functor Fwd where
>   fmap = fmapDefault
>
> instance Foldable Fwd where
>   foldMap = foldMapDefault

%endif
