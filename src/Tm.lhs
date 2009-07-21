\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Tm where

> import Control.Applicative
> import Data.Foldable hiding (foldl)
> import Data.Traversable
> import Data.Either
> import Control.Monad

> import BwdFwd
> import Features

%endif

%format :$ = ":\!\$"
%format :? = "\,:\!\!\!\in"
%format Set = "\star"
%format Pi = "\Pi"
%format :. = "\bullet"

\subsection{Syntax of Terms and Values}

> data Dir    = In | Ex

We distinguish |In|Terms (into which we push types) and |Ex|Terms
(from which we infer types).

> data Phase  = TT | VV

We distinguish the representations of |TT| terms and |VV| values.

And, of course, we're polymorphic in the representation of free variables,
like your mother always told you.

> data Tm :: {Dir, Phase} -> * -> * where
>   L     :: Scope p x           -> Tm {In, p} x   -- \(\lambda\)
>   C     :: Can (Tm {In, p} x)  -> Tm {In, p} x   -- canonical
>   N     :: Tm {Ex, p} x        -> Tm {In, p} x   -- |Ex| to |In|
>   P     :: x                   -> Tm {Ex, p} x   -- parameter
>   V     :: Int                 -> Tm {Ex, TT} x  -- variable
>   (:$)  :: Tm {Ex, p} x -> Elim (Tm {In, p} x) -> Tm {Ex, p} x -- elimination
>   (:@)  :: Op -> [Tm {In, p} x] -> Tm {Ex, p} x  -- fully applied operator
>   (:?)  :: Tm {In, TT} x -> Tm {In, TT} x -> Tm {Ex, TT} x     -- typing
>
> data Scope :: {Phase} -> * -> * where
>   (:.)  :: String -> Tm {In, TT} x         -> Scope {TT} x  -- binding
>   H     :: Env -> String -> Tm {In, TT} x  -> Scope {VV} x  -- closure
>   K     :: Tm {In, p} x                    -> Scope p x     -- constant
>
> data Can :: * -> * where
>   Set   :: Can t                                        -- set of sets
>   Pi    :: t -> t -> Can t                              -- functions
>   import <- CanConstructors
>   deriving (Show, Eq)
>
> data Elim :: * -> * where
>   A     :: t -> Elim t                                  -- application
>   import <- ElimConstructors
>   deriving (Show, Eq)
>
> data Op = Op
>   { opName  :: String, opArity :: Int
>   , opTy    :: forall t. (t -> VAL) -> [t] -> Maybe ([VAL :>: t] , VAL)
>   , opRun   :: [VAL] -> Either NEU VAL
>   }

We have some pattern synonyms for common, er, patterns.

> pattern SET       = C Set                   -- set of sets
> pattern Arr s t   = C (Pi s (L (K t)))      -- simple arrow
> pattern PI x s t  = C (Pi s (L (x :. t)))   -- dependent functions
> import <- CanPats

We have some type synonyms for commonly occurring instances of |Tm|.

> type InTm  = Tm {In, TT}
> type ExTm  = Tm {Ex, TT}
> type INTM  = InTm REF
> type EXTM  = ExTm REF
> type VAL   = Tm {In, VV} REF
> type NEU   = Tm {Ex, VV} REF
> type Env   = Bwd VAL

> data Irr x = Irr x deriving Show

> instance Eq (Irr x) where
>   _ == _ = True

> instance Eq x => Eq (Tm {d, TT} x) where
>   L s0          == L s1          = s0 == s1
>   C c0          == C c1          = c0 == c1
>   N n0          == N n1          = n0 == n1
>   P x0          == P x1          = x0 == x1
>   V i0          == V i1          = i0 == i1
>   (t0 :$ e0)    == (t1 :$ e1)    = t0 == t1 && e0 == e1
>   (op0 :@ vs0)  == (op1 :@ vs1)  = op0 == op1 && vs0 == vs1
>   (t0 :? _)     == (t1 :? _)     = t0 == t1
>   _             == _             = False

> instance Eq x => Eq (Scope {TT} x) where
>   (_ :. t0)  == (_ :. t1)  = t0 == t1
>   K t0       == K t1       = t0 == t1
>   _          == _          = False

> instance Eq Op where
>   op0 == op1 = opName op0 == opName op1

> type Spine p x = [Elim (Tm {In, p} x)]
> ($:$) :: Tm {Ex, p} x -> Spine p x -> Tm {Ex, p} x
> ($:$) = foldl (:$)

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
>   =  DECL VAL
>   |  DEFN VAL VAL
>   |  HOLE VAL
>   deriving Show

We have special pairs for types going in and coming out of stuff.

> data y :>: t = y :>: t
> data t :<: y = t :<: y

> ($$) :: VAL -> Elim VAL -> VAL
> L (K v)      $$ A _  = v
> L (H g _ t)  $$ A v  = eval t (g :< v)
> import <- ElimComputation
> N n          $$ e    = N (n :$ e)

> (@@) :: Op -> [VAL] -> VAL
> op @@ vs = either (\_ -> N (op :@ vs)) id (opRun op vs) 

> pval :: REF -> VAL
> pval (_ := DEFN v _)  = v
> pval r                = N (P r)

> body :: Scope {TT} REF -> Env -> Scope {VV} REF
> body (K v)     g = K (eval v g)
> body (x :. t)  g = H g x t

> eval :: Tm {d, TT} REF -> Env -> VAL
> eval (L b)       = (|L (body b)|)
> eval (C c)       = (|C (eval ^$ c)|)
> eval (N n)       = eval n
> eval (P x)       = (|(pval x)|)
> eval (V i)       = (!. i)
> eval (t :$ e)    = (|eval t $$ (eval ^$ e)|)
> eval (op :@ vs)  = (|(op @@) (eval ^$ vs)|)
> eval (t :? _)    = eval t

> evTm :: Tm {d, TT} REF -> VAL
> evTm t = eval t B0

> data Mangle f x y = Mang
>   {  mangP :: x -> f [Elim (InTm y)] -> f (ExTm y)
>   ,  mangV :: Int -> f [Elim (InTm y)] -> f (ExTm y)
>   ,  mangB :: String -> Mangle f x y
>   }

> (%) :: Applicative f => Mangle f x y -> Tm {In, TT} x -> f (Tm {In, TT} y)
> m % L (K t)      = (|L (|K (m % t)|)|)
> m % L (x :. t)   = (|L (|(x :.) (mangB m x % t)|)|)
> m % C c          = (|C ((m %) ^$ c)|)
> m % N n          = (|N (exMang m n (|[]|))|)

> exMang ::  Applicative f => Mangle f x y ->
>            Tm {Ex, TT} x -> f [Elim (Tm {In, TT} y)] -> f (Tm {Ex, TT} y)
> exMang m (P x)     es = mangP m x es
> exMang m (V i)     es = mangV m i es
> exMang m (o :@ a)  es = (|(| (o :@) ((m %) ^$ a) |) $:$ es|) 
> exMang m (t :$ e)  es = exMang m t (|((m %) ^$ e) : es|)
> exMang m (t :? y)  es = (|(|(m % t) :? (m % y)|) $:$ es|)

> capture :: Bwd String -> Mangle I String String
> capture xs = Mang
>   {  mangP = \ x ies  -> (|(either P V (h xs x) $:$) ies|)
>   ,  mangV = \ i ies  -> (|(V i $:$) ies|)
>   ,  mangB = \ x -> capture (xs :< x)
>   } where
>   h B0         x  = Left x
>   h (ys :< y)  x
>     | x == y      = Right 0
>     | otherwise   = (|succ (h ys y)|)

> under :: Int -> x -> Mangle I x x
> under i y = Mang
>   {  mangP = \ x ies -> (|(P x $:$) ies|)
>   ,  mangV = \ j ies -> (|((if i == j then P y else V j) $:$) ies|)
>   ,  mangB = \ _ -> under (i + 1) y
>   }

> underScope :: Scope {TT} REF -> REF -> INTM
> underScope (K t)     _ = t
> underScope (_ :. t)  x = unI (under 0 x % t)

%if False

> newtype I x = I {unI :: x} deriving (Show, Eq)
> instance Functor I where
>   fmap f (I s) = I (f s)
> instance Applicative I where
>   pure         = I
>   I f <*> I s  = I (f s)

> instance Applicative (Either x) where
>   pure = return
>   (<*>) = ap
> instance Monad (Either x) where
>   return = Right
>   Left x   >>= _  = Left x
>   Right y  >>= f  = f y

> instance Traversable Can where
>   traverse f Set       = (|Set|)
>   traverse f (Pi s t)  = (|Pi (f s) (f t)|)
>   import <- TraverseCan
>
> instance Functor Can where
>   fmap = fmapDefault
> instance Foldable Can where
>   foldMap = foldMapDefault

> instance Traversable Elim where
>   traverse f (A s)  = (|A (f s)|)
>   import <- TraverseElim

> instance Functor Irr where
>   fmap = fmapDefault
> instance Foldable Irr where
>   foldMap = foldMapDefault
> instance Traversable Irr where
>    traverse f (Irr x) = (|Irr (f x)|)

> instance Functor Elim where
>   fmap = fmapDefault
> instance Foldable Elim where
>   foldMap = foldMapDefault

> instance Show x => Show (Tm dp x) where
>   show (L s)       = "L (" ++ show s ++ ")"
>   show (C c)       = "C (" ++ show c ++ ")"
>   show (N n)       = "N (" ++ show n ++ ")"
>   show (P x)       = "P (" ++ show x ++ ")"
>   show (V i)       = "V " ++ show i
>   show (n :$ e)    = "(" ++ show n ++ " :$ " ++ show e ++ ")"
>   show (op :@ vs)  = "(" ++ opName op ++ " :@ " ++ show vs ++ ")"
>   show (t :? y)    = "(" ++ show t ++ " :? " ++ show y ++ ")"
>
> instance Show x => Show (Scope p x) where
>   show (x :. t)   = show x ++ " :. " ++ show t
>   show (H g x t)  =
>     "H (" ++ show g ++ ") " ++ show x ++ " (" ++ show t ++ ")"
>   show (K t) = "K (" ++ show t ++")"


%endif
