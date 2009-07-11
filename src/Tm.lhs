\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances #-}

> module Tm where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> import BwdFwd

%endif

%format :- = ":\!\!\!-"
%format :? = "\,:\!\!\!\in"
%format Set = "\star"
%format Pi = "\Pi"
%format :. = "\bullet"

> data Dir    = In | Ex
> data Phase  = TT | VV

> data Tm :: {Dir, Phase} -> * -> * where
>   L     :: Scope p x           -> Tm {In, p} x   -- \(\lambda\)
>   C     :: Can (Tm {In, p} x)  -> Tm {In, p} x   -- canonical
>   N     :: Tm {Ex, p} x        -> Tm {In, p} x   -- |Ex| to |In|
>   P     :: x                   -> Tm {Ex, p} x   -- parameter
>   V     :: Int                 -> Tm {Ex, TT} x  -- variable
>   (:-)  :: Tm {Ex, p} x -> Elim (Tm {In, p} x) -> Tm {Ex, p} x  -- elimination
>   (:?)  :: Tm {In, TT} x -> Tm {In, TT} x -> Tm {Ex, TT} x      -- typing
>
> data Scope :: {Phase} -> * -> * where
>   (:.)  :: String -> Tm {In, TT} x         -> Scope {TT} x  -- binding
>   H     :: Env -> String -> Tm {In, TT} x  -> Scope {VV} x  -- closure
>   K     :: Tm {In, p} x                    -> Scope p x     -- constant
>
> data Can :: * -> * where
>   Set   :: Can t                                        -- set of sets
>   Pi    :: t -> t -> Can t                              -- functions
>   deriving (Show, Eq)
>
> data Elim :: * -> * where
>   A :: t -> Elim t                                      -- application
>   deriving (Show, Eq)

> pattern Arr s t   = C (Pi s (L (K t)))      -- simple arrow

> type InTm  = Tm {In, TT}
> type ExTm  = Tm {Ex, TT}
> type INTM  = InTm REF
> type EXTM  = ExTm REF
> type VAL   = Tm {In, VV} REF
> type NEU   = Tm {Ex, VV} REF
> type Env   = Bwd VAL

> data REF = Name := RKind  -- is shared where possible
>
> type Name = [(String, Int)]
>
> instance Show REF where
>   show (n := _) = show n
>
> instance Eq REF where
>   (x := _) == (y := _) = x == y  -- could use cheeky pointer equality?

> data RKind
>   = DECL VAL
>   | DEFN VAL VAL
>   | HOLE VAL
>   deriving Show

> ($-) :: VAL -> Elim VAL -> VAL
> L (K v)      $- A _  = v
> L (H g _ t)  $- A v  = eval t (g :< v)
> N n          $- e    = N (n :- e)

> pval :: REF -> VAL
> pval (_ := DEFN v _)  = v
> pval r                = N (P r)

> body :: Scope {TT} REF -> Env -> Scope {VV} REF
> body (K v)     g = K (eval v g)
> body (x :. t)  g = H g x t

> eval :: Tm {d, TT} REF -> Env -> VAL
> eval (L b)     = (|L (body b)|)
> eval (C c)     = (|C (eval ^$ c)|)
> eval (N n)     = eval n
> eval (P x)     = (|(pval x)|)
> eval (V i)     = (!. i)
> eval (t :- e)  = (|eval t $- (eval ^$ e)|)
> eval (t :? _)  = eval t


%if False

> instance Traversable Can where
>   traverse f Set       = (|Set|)
>   traverse f (Pi s t)  = (|Pi (f s) (f t)|)
>
> instance Functor Can where
>   fmap = fmapDefault
> instance Foldable Can where
>   foldMap = foldMapDefault

> instance Traversable Elim where
>   traverse f (A s)  = (|A (f s)|)
>
> instance Functor Elim where
>   fmap = fmapDefault
> instance Foldable Elim where
>   foldMap = foldMapDefault

> instance Show x => Show (Tm dp x) where
>   show (L s)     = "L (" ++ show s ++ ")"
>   show (C c)     = "C (" ++ show c ++ ")"
>   show (N n)     = "N (" ++ show n ++ ")"
>   show (P x)     = "P (" ++ show x ++ ")"
>   show (V i)     = "V " ++ show i
>   show (n :- e)  = "(" ++ show n ++ " :- " ++ show e ++ ")"
>   show (t :? y)  = "(" ++ show t ++ " :? " ++ show y ++ ")"
>
> instance Show x => Show (Scope p x) where
>   show (x :. t)   = show x ++ " :. " ++ show t
>   show (H g x t)  =
>     "H (" ++ show g ++ ") " ++ show x ++ " (" ++ show t ++ ")"
>   show (K t) = "K (" ++ show t ++")"

%endif