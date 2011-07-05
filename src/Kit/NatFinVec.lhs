\subsection{NatFinVec}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TypeOperators, TypeFamilies, FlexibleContexts,
>     MultiParamTypeClasses, UndecidableInstances, ScopedTypeVariables,
>     RankNTypes, FlexibleInstances, OverlappingInstances, TypeFamilies #-}

> module Kit.NatFinVec where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> import Kit.BwdFwd

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
>   (:>>:)  :: x -> Vec {n} x -> Vec {S n} x
>   deriving ()

> infixr 4 :>>:

> data BVec :: {Nat} -> * -> * where
>   BV0     :: BVec {Z} x
>   (:<<<:)  :: BVec {n} x -> x -> BVec {S n} x
>   deriving ()

> infixr 4 :<<<:

> instance Functor (BVec {n}) where
>     fmap = fmapDefault

> instance Foldable (BVec {n}) where
>     foldMap = foldMapDefault

> instance Traversable (BVec {n}) where
>     traverse f BV0           = (| BV0 |)
>     traverse f (xs :<<<: x)  = (| (traverse f xs) :<<<: f x |)



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
> (x :>>: xs) !>! Fz    = x
> (x :>>: xs) !>! Fs i  = xs !>! i

> (!<!) :: Eq x => x -> Vec {n} x -> Maybe (Fin {n})
> x !<! (x' :>>: xs) | x == x'  = (| Fz |)
> x !<! (_ :>>: xs)             = (| Fs (x !<! xs) |)
> _ !<! _                       = (|)

> instance Show x => Show (Vec {n} x) where
>   show V0          = "V0"
>   show (x :>>: xs)  = show x ++ " :>>: " ++ show xs

> instance Functor (Vec {n}) where
>   fmap f V0          = V0
>   fmap f (x :>>: xs)  = f x :>>: fmap f xs

> instance {:n :: Nat:} => Applicative (Vec {n}) where
>   pure = vec {:n :: Nat:} where
>     vec :: forall x. pi (n :: Nat). x -> Vec {n} x
>     vec {Z}    x = V0
>     vec {S n}  x = x :>>: vec n x
>   (<*>) = vapp where
>     vapp :: Vec {m} (s -> t) -> Vec {m} s -> Vec {m} t
>     vapp V0          V0          = V0
>     vapp (f :>>: fs)  (s :>>: ss)  = f s :>>: vapp fs ss

> vhead :: Vec {S n} x -> x
> vhead (x :>>: xs) = x

> vtail :: Vec {S n} x -> Vec {n} x
> vtail (x :>>: xs) = xs

> instance {:n :: Nat:} => Monad (Vec {n}) where
>   return = pure
>   (>>=) = vdiag where
>     vdiag :: Vec {m} a -> (a -> Vec {m} b) -> Vec {m} b
>     vdiag V0          f = V0
>     vdiag (x :>>: xs)  f = vhead (f x) :>>: vdiag xs (vtail . f)

> instance Traversable (Vec {n}) where
>   traverse f V0          = (| V0 |)
>   traverse f (x :>>: xs)  = (| f x :>>: traverse f xs |)

> instance Foldable (Vec {n}) where
>   foldMap = foldMapDefault

> class Leq (m :: {Nat}) (n :: {Nat}) where
>   finj :: Fin {m} -> Fin {n}

> instance Leq n n where
>   finj = id

> instance (o ~ {S n}, Leq m n) => Leq m o where
>   finj = Fs . finj

> bound :: pi (n :: Nat) . Int -> Maybe (Fin {n})
> bound {Z} _ = Nothing
> bound {S n} 0 = (| Fz |)
> bound {S n} m = (| Fs (bound {n} (m - 1)) |)

> mkInt :: pi (n :: Nat) . Int
> mkInt {Z} = 0
> mkInt {S n} = 1 + mkInt n

> intNat :: Int -> (pi (n :: Nat) . a) -> a
> intNat 0 f = f {Z}
> intNat n f = intNat (n-1) (\ m -> f {S m})

> emb :: Fin {n} -> Fin {S n}
> emb Fz = Fz
> emb (Fs i) = Fs (emb i)

> fmax' :: pi (n :: Nat). Fin {S n}
> fmax' {Z} = Fz
> fmax' {S n} = Fs (fmax' {n}) 

> fmax :: {: n :: Nat :} => Fin {S n}
> fmax = fmax' {: n :: Nat :}

> vUpTo :: pi (n :: Nat) . Vec {n} Int
> vUpTo {n} = help {n} 0
>   where
>     help :: pi (n :: Nat). Int -> Vec {n} Int
>     help {Z} m = V0
>     help {S n} m = m :>>: help {n} (m+1)

> vUpTo' :: {:n :: Nat:} => Vec {n} Int
> vUpTo' = vUpTo {:n :: Nat:}

> vUpToF :: pi (n :: Nat) . Vec {n} (Fin {n})
> vUpToF {n} = help {n} 
>   where
>     help :: pi (n :: Nat).  Vec {n} (Fin {n})
>     help {Z} = V0
>     help {S n} = Fz :>>: fmap Fs (help {n})

> vUpToF' :: {:n :: Nat:} => Vec {n} (Fin {n}) 
> vUpToF' = vUpToF {:n :: Nat:}

> vDownFromF :: pi (n :: Nat) . Vec {n} (Fin {n})
> vDownFromF {n} = help {n} 
>   where
>     help :: pi (n :: Nat).  Vec {n} (Fin {n})
>     help {Z} = V0
>     help {S n} = fmax' {n} :>>: fmap emb (help {n})

> vDownFromF' :: {:n :: Nat:} => Vec {n} (Fin {n}) 
> vDownFromF' = vDownFromF {:n :: Nat:}

> bvDownFromF :: pi (n :: Nat) . BVec {n} (Fin {n})
> bvDownFromF {n} = help {n} 
>   where
>     help :: pi (n :: Nat).  BVec {n} (Fin {n})
>     help {Z} = BV0
>     help {S n} = fmap Fs (help {n}) :<<<: Fz

> bvDownFromF' :: {:n :: Nat:} => BVec {n} (Fin {n}) 
> bvDownFromF' = bvDownFromF {:n :: Nat:}

> listVec :: [a] -> (pi (n :: Nat). Vec {n} a -> t) -> t
> listVec [] f = f {Z} V0
> listVec (x : xs) f = listVec xs (\ n ys -> f {S n} (x :>>: ys))

> fwdVec :: Fwd a -> (pi (n :: Nat). Vec {n} a -> t) -> t
> fwdVec F0 f = f {Z} V0
> fwdVec (x :> xs) f = fwdVec xs (\ n ys -> f {S n} (x :>>: ys))

> bwdVec :: Bwd a -> (pi (n :: Nat). BVec {n} a -> t) -> t
> bwdVec B0 f = f {Z} BV0
> bwdVec (xs :< x) f = bwdVec xs (\ n ys -> f {S n} (ys :<<<: x))


> vlength :: Vec {n} a -> Int
> vlength V0 = 0
> vlength (_ :>>: xs) = 1 + vlength xs

