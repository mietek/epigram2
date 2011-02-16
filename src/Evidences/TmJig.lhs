\subsection{TmJig}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, FunctionalDependencies,
>     OverlappingInstances, UndecidableInstances, TypeFamilies #-}

> module Evidences.TmJig where

> import Prelude hiding (foldl)

> import Control.Applicative
> import Control.Monad.Error
> import qualified Data.Monoid as M
> import Data.Foldable
> import Data.List hiding (foldl)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Evidences.Tm
> import Evidences.NameSupply

%endif


> class Leq (m :: {Nat}) (n :: {Nat}) where
>   finj :: Fin {m} -> Fin {n}

> instance Leq n n where
>   finj = id

> instance (o ~ {S n}, Leq m n) => Leq m o where
>   finj = Fs . finj

> class Wrapper (t :: *) (n :: {Nat}) | t -> n where
>   wrapper :: Tm {Head, Exp, n} -> Bwd (Tm {Body, Exp, n}) -> t

> instance Wrapper (Tm {Body, Exp, n}) n where
>   wrapper h es = h :$ es

> instance (s ~ Tm {Body, Exp, n}, Wrapper t n) => Wrapper (s -> t) n where
>   wrapper f es e = wrapper f (es :< e) 

 instance (Wrapper s n, Wrapper t n) => Wrapper (s, t) n where
   wrapper f es = (wrapper f es, wrapper f es)

> cough :: (Fin {S m} -> Tm {p, b, m}) -> Tm {p, b, m}
> cough f = f Fz  -- coughs up the zero you want

> la ::  String ->
>        ((forall t n. (Wrapper t n, Leq {S m} n) => t)
>          -> Tm {Body, Exp, S m}) ->
>        Tm {Body, s, m}
> la s b = cough $ \ fz -> L ENil s (b (wrapper (V (finj fz)) B0))

> (->>) :: (String, Tm {Body, s, m}) ->
>          ((forall t n. (Wrapper t n, Leq {S m} n) => t)
>            -> Tm {Body, Exp, S m}) ->
>        Tm {Body, s, m}
> (x, s) ->> t = PI s (la x t)

> (-**) :: (String, Tm {Body, s, m}) ->
>          ((forall t n. (Wrapper t n, Leq {S m} n) => t)
>            -> Tm {Body, Exp, S m}) ->
>        Tm {Body, s, m}
> (x, s) -** t = SIGMA s (la x t)

> ugly :: Vec {n} String -> Tm {p, s, n} -> String
> ugly xs (L ENil x b) = "(\\ " ++ x ++ " -> " ++ ugly (x :>: xs) b ++ ")"
> ugly xs (LK e)       = "(\\ _ -> " ++ ugly xs e ++ ")"
> ugly xs (ARR s t) = "(" ++ ugly xs s ++ " -> " ++ ugly xs t ++ ")"
> ugly xs (PI s (L ENil x t)) = "((" ++ x ++ " : " ++ ugly xs s ++ ") -> "
>                              ++ ugly (x :>: xs) t ++ ")"
> ugly xs (TIMES s t) = "(" ++ ugly xs s ++ " * " ++ ugly xs t ++ ")"
> ugly xs (SIGMA s (L ENil x t)) = "((" ++ x ++ " : " ++ ugly xs s ++ ") * "
>                              ++ ugly (x :>: xs) t ++ ")"
> ugly xs SET = "Set"
> ugly xs (h :$ B0) = ugly xs h
> ugly xs (h :$ es) = "(" ++ ugly xs h ++ foldMap (\ e -> " " ++ ugly xs e) es ++ ")"
> ugly xs (V i) = xs !>! i
> ugly xs (P (i, t)) = "!" ++ show i
> ugly xs (D (s, _, _) B0 _) = s
> ugly xs (D (s, _, _) es _) = "(" ++ s ++ foldMap (\ e -> " " ++ ugly V0 e) es ++ ")"
> ugly xs (ENil :/ e) = ugly xs e
> ugly _ _ = "???"

