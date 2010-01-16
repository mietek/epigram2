\section{Missing Library}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
> {-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, UndecidableInstances, TypeSynonymInstances #-}

> module Kit.MissingLibrary where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.Identity
> import Control.Monad.State
> import Control.Monad.Reader

> import Data.Foldable
> import Data.List
> import Data.Monoid
> import Data.Traversable

%endif

\subsection{Indicator Function}

> indicator :: (x -> Bool) -> x -> Int
> indicator p x = if p x then 1 else 0

\subsection{Newtype Unwrapping}

> class Newtype n where
>   type Unwrap n
>   wrap :: Unwrap n -> n
>   unwrap :: n -> Unwrap n

> ala :: Newtype v' =>
>        (t -> t') -> ((s -> t') -> u -> v') -> (s -> t) -> u -> Unwrap v'
> ala p h f u = unwrap (h (p . f) u)

> instance Newtype (Sum a) where
>   type Unwrap (Sum a) = a
>   wrap    = Sum
>   unwrap  = getSum

> instance Newtype (Endo a) where
>   type Unwrap (Endo a) = a -> a
>   wrap    = Endo
>   unwrap  = appEndo

> newtype AppLift a x = AppLift (a x)

> instance (Applicative a, Monoid x) => Monoid (AppLift a x) where
>   mempty = AppLift (pure mempty)
>   mappend (AppLift ax) (AppLift ay) = AppLift (mappend <$> ax <*> ay)

> instance Newtype (AppLift a x) where
>   type Unwrap (AppLift a x) = a x
>   wrap = AppLift
>   unwrap (AppLift ax) = ax


\subsection{Error Handling}

> type StackError = [String]

> instance MonadError StackError Maybe where
>   throwError _ = Nothing
>   catchError (Just x)  _ = Just x
>   catchError Nothing   f = f []

> instance Error StackError where
>   strMsg s = [s]


> catchMaybe :: MonadError [e] m => Maybe a -> e -> m a
> catchMaybe (Just x)  _ = return x
> catchMaybe Nothing   s = throwError [s]

> catchEither :: MonadError [e] m => Either [e] a -> e -> m a
> catchEither (Right x) _ = return x
> catchEither (Left s) e = throwError (e : s)


> throwError' :: MonadError [e] m => e -> m a
> throwError' e = throwError [e]

> replaceError :: MonadError [e] m => m a -> e -> m a
> replaceError c e = catchError c (\x -> throwError (e:x))

> replacePMF :: MonadError [String] m => m a -> String -> m a
> replacePMF c s = catchError c f
>   where
>     f (x:xs) =  if "Pattern match failure" `isPrefixOf` x
>                 then throwError' s
>                 else throwError (x:xs)
>     f [] = throwError []

\subsection{Missing Applicatives}

Ah, if only 

< instance Monad m => Applicative m 

were possible. Unfortunately it isn't (at least without |UndecidableInstances|)
so we have to do things the long way...

> instance Error x => Applicative (Either x) where
>   pure = return
>   (<*>) = ap

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap

> instance Applicative Identity where
>   pure = return
>   (<*>) = ap

> instance Monad m => Applicative (ReaderT r m) where
>     pure = return 
>     (<*>) = ap

> instance MonadPlus m => Alternative (ReaderT r m) where
>     empty = mzero
>     (<|>) = mplus

\subsection{Missing Instances}

> instance Traversable (Either x) where
>     traverse g (Left a) = pure (Left a)
>     traverse g (Right b) = Right <$> g b

> instance Foldable (Either x) where
>     foldMap = foldMapDefault


\subsection{HalfZip}

> class Functor f => HalfZip f where
>   halfZip :: f x -> f y -> Maybe (f (x,y))

\subsection{Functor Kit}

> newtype Id       x = Id {unId :: x}        deriving Show
> newtype Ko a     x = Ko {unKo :: a}        deriving Show
> data (p :+: q)  x = Le (p x) | Ri (q x)    deriving Show
> data (p :*: q)  x = p x :& q x             deriving Show

> instance Functor Id where
>   fmap f (Id x) = Id (f x)

> instance Functor (Ko a) where
>   fmap f (Ko a) = Ko a

> instance (Functor p, Functor q) => Functor (p :+: q) where
>   fmap f (Le px)  = Le (fmap f px)
>   fmap f (Ri qx)  = Ri (fmap f qx)

> instance (Functor p, Functor q) => Functor (p :*: q) where
>   fmap f (px :& qx)  = fmap f px :& fmap f qx

> instance Foldable Id where
>   foldMap = foldMapDefault

> instance Foldable (Ko a) where
>   foldMap = foldMapDefault

> instance (Traversable p, Traversable q, Foldable p, Foldable q) => Foldable (p :+: q) where
>   foldMap = foldMapDefault

> instance (Traversable p, Traversable q, Foldable p, Foldable q) => Foldable (p :*: q) where
>   foldMap = foldMapDefault

> newtype Fix f = InF (f (Fix f))  -- tying the knot

> instance Show (f (Fix f)) => Show (Fix f) where
>   show (InF x) = "InF (" ++ show x ++ ")"

> rec :: Functor f => (f v -> v) -> Fix f -> v
> rec m (InF fd) = m
>     (fmap (rec m {- :: Fix f -> v -})
>           (fd {- :: f (Fix f)-})
>      {- :: f v -})

> instance Traversable Id where
>   traverse f (Id x) = Id <$> f x

> instance Traversable (Ko a) where
>   traverse f (Ko c) = pure (Ko c)

> instance (Traversable p, Traversable q) => Traversable (p :+: q) where
>   traverse f (Le px)  = Le <$> traverse f px
>   traverse f (Ri qx)  = Ri <$> traverse f qx

> instance (Traversable p, Traversable q) => Traversable (p :*: q) where
>   traverse f (px :& qx)  = (:&) <$> traverse f px <*> traverse f qx

> instance Applicative Id where  -- makes fmap from traverse
>   pure = Id
>   Id f <*> Id s = Id (f s)

> instance Monoid c => Applicative (Ko c) where-- makes crush from traverse
>   -- pure :: x -> K c x
>   pure x = Ko mempty
>   -- (<*>) :: K c (s -> t) -> K c s -> K c t
>   Ko f <*> Ko s = Ko (mappend f s)

> crush :: (Traversable f, Monoid c) => (x -> c) -> f x -> c
> crush m fx = unKo $ traverse (Ko . m) fx

> reduce :: (Traversable f, Monoid c) => f c -> c
> reduce = crush id

> instance Monoid Int where
>   mempty = 0
>   mappend = (+)

> size :: (Functor f, Traversable f) => Fix f -> Int
> size = rec ((1+) . reduce)

> instance HalfZip Id where
>   halfZip (Id x) (Id y) = (| (Id (x,y)) |)

> instance (Eq a) => HalfZip (Ko a) where
>   halfZip (Ko x) (Ko y) | x == y = (| (Ko x) |)
>   halfZip _ _ = Nothing  

> instance (HalfZip p, HalfZip q) => HalfZip (p :+: q) where
>   halfZip (Le x) (Le y) = (|Le (halfZip x y)|)
>   halfZip (Ri x) (Ri y) = (|Ri (halfZip x y)|)
>   halfZip _ _ = Nothing  

> instance (HalfZip p, HalfZip q) => HalfZip (p :*: q) where
>   halfZip (x0 :& y0) (x1 :& y1) = (| (halfZip x0 x1) :& (halfZip y0 y1) |)



%if False

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

%endif
