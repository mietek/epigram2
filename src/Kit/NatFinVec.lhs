\subsection{NatFinVec}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TypeOperators, TypeFamilies, FlexibleContexts,
>     MultiParamTypeClasses, UndecidableInstances, ScopedTypeVariables,
>     RankNTypes #-}

> module Kit.NatFinVec where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> import ShePrelude

%endif

> data Nat :: * where
>   Z :: Nat
>   S :: Nat -> Nat
>   deriving (SheSingleton)

> data Fin :: {Nat} -> * where
>   Fz :: Fin {S n}
>   Fs :: Fin n -> Fin {S n}
>   deriving ()

> data Vec :: {Nat} -> * -> * where
>   V0     :: Vec {Z} x
>   (:>:)  :: x -> Vec {n} x -> Vec {S n} x
>   deriving ()

> infixr 4 :>:

> fog :: Fin {n} -> Int
> fog Fz = 0
> fog (Fs i) = 1 + fog i

> instance Show (Fin {n}) where
>   show x = show (fog x)

> instance Eq (Fin {n}) where
>   Fz == Fz = True
>   Fs i == Fs j = i == j
>   _ == _ = False

> (!>!) :: Vec {n} x -> Fin {n} -> x
> (x :>: xs) !>! Fz    = x
> (x :>: xs) !>! Fs i  = xs !>! i

> instance Show x => Show (Vec {n} x) where
>   show V0          = "V0"
>   show (x :>: xs)  = show x ++ " :>: " ++ show xs

> instance Functor (Vec {n}) where
>   fmap f V0          = V0
>   fmap f (x :>: xs)  = f x :>: fmap f xs

> instance {:n :: Nat:} => Applicative (Vec {n}) where
>   pure = vec {:n :: Nat:} where
>     vec :: forall x. pi (n :: Nat). x -> Vec {n} x
>     vec {Z}    x = V0
>     vec {S n}  x = x :>: vec n x
>   (<*>) = vapp where
>     vapp :: Vec {m} (s -> t) -> Vec {m} s -> Vec {m} t
>     vapp V0          V0          = V0
>     vapp (f :>: fs)  (s :>: ss)  = f s :>: vapp fs ss

> vhead :: Vec {S n} x -> x
> vhead (x :>: xs) = x

> vtail :: Vec {S n} x -> Vec {n} x
> vtail (x :>: xs) = xs

> instance {:n :: Nat:} => Monad (Vec {n}) where
>   return = pure
>   (>>=) = vdiag where
>     vdiag :: Vec {m} a -> (a -> Vec {m} b) -> Vec {m} b
>     vdiag V0          f = V0
>     vdiag (x :>: xs)  f = vhead (f x) :>: vdiag xs (vtail . f)

> instance Traversable (Vec {n}) where
>   traverse f V0          = (| V0 |)
>   traverse f (x :>: xs)  = (| f x :>: traverse f xs |)

> instance Foldable (Vec {n}) where
>   foldMap = foldMapDefault
