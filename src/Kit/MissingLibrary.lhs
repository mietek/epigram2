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
> import Control.Monad.Writer

> import Data.Foldable
> import Data.Traversable

%endif


\subsection{Renaming}

> trail :: (Applicative f, Foldable t, Monoid (f a)) => t a -> f a
> trail = foldMap pure

> (<+>) :: Monoid x => x -> x -> x
> (<+>) = mappend

> (^$) :: (Traversable f, Applicative i) => (s -> i t) -> f s -> i (f t)
> (^$) = traverse

> iter :: (a -> b -> b) -> [a] -> b -> b
> iter = flip . Prelude.foldr


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

> instance Newtype (Id a) where
>   type Unwrap (Id a) = a
>   wrap = Id
>   unwrap = unId

> instance Newtype Any where
>   type Unwrap Any = Bool
>   wrap    = Any
>   unwrap  = getAny

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

> catchMaybe :: MonadError [e] m => Maybe a -> e -> m a
> catchMaybe (Just x)  _ = return x
> catchMaybe Nothing   s = throwError [s]

> catchEither :: MonadError [e] m => Either [e] a -> e -> m a
> catchEither (Right x) _ = return x
> catchEither (Left s) e = throwError (e : s)


> throwError' :: MonadError [e] m => e -> m a
> throwError' e = throwError [e]

> pushError :: MonadError [e] m => m a -> e -> m a
> pushError c e = catchError c (\x -> throwError (e:x))


\subsection{Missing Applicatives}

Ah, if only 

< instance Monad m => Applicative m 

were possible. Unfortunately it isn't (at least without |UndecidableInstances|)
so we have to do things the long way...


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

> instance Monad m => Applicative (StateT r m) where
>     pure = return 
>     (<*>) = ap

> instance MonadPlus m => Alternative (StateT r m) where
>     empty = mzero
>     (<|>) = mplus

> instance Error x => Applicative (Either x) where
>   pure = return
>   (<*>) = ap

> instance Error x => Alternative (Either x) where
>     empty = Left $ strMsg "empty alternative"
>     (Left _) <|> p = p
>     p@(Right _) <|> _ = p


\subsection{Missing Instances}

> instance Traversable (Either x) where
>     traverse g (Left a) = pure (Left a)
>     traverse g (Right b) = Right <$> g b

> instance Foldable (Either x) where
>     foldMap = foldMapDefault

> instance (Applicative f, Num x, Show (f x), Eq (f x)) => Num (f x) where
>   x + y          = (|x + y|)
>   x * y          = (|x * y|)
>   x - y          = (|x - y|)
>   abs x          = (|abs x|)
>   negate x       = (|negate x|)
>   signum x       = (|signum x|)
>   fromInteger i  = (|(fromInteger i)|)

> instance Monoid o => Applicative (Writer o) where
>   pure = return
>   (<*>) = ap

Grr.

> instance Monoid (IO ()) where
>   mempty = return ()
>   mappend x y = do x; y


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


\subsection{Applicative Kit}

The |untilA| operator runs its first argument one or more times until
its second argument succeeds, at which point it returns the result. If
the first argument fails, the whole operation fails. If you have
understood |untilA|, it won't take you long to understand |whileA|.

> untilA :: Alternative f => f () -> f a -> f a
> g `untilA` test = g *> try
>     where try = test <|> (g *> try)
>
> whileA :: Alternative f => f () -> f a -> f a
> g `whileA` test = try
>     where try = test <|> (g *> try)



The |much| operator runs its argument until it fails, then returns the state of
its last success. It is very similar to |many|, except that it throws away the
results.

> much :: Alternative f => f () -> f ()
> much f = (f *> much f) <|> pure ()


\subsection{Monadic Kit}

> ignore :: Monad m => m a -> m ()
> ignore f = do
>     f
>     return ()
