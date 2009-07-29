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
> import MissingLibrary
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
>   L     :: Scope p x             -> Tm {In, p} x   -- \(\lambda\)
>   C     :: Can (Tm {In, p} x)    -> Tm {In, p} x   -- canonical
>   N     :: Tm {Ex, p} x          -> Tm {In, p} x   -- |Ex| to |In|
>   P     :: x                     -> Tm {Ex, p} x   -- parameter
>   V     :: Int                   -> Tm {Ex, TT} x  -- variable
>   (:@)  :: Op -> [Tm {In, p} x]  -> Tm {Ex, p} x   -- fully applied op
>   (:$)  :: Tm {Ex, p} x -> Elim (Tm {In, p} x) -> Tm {Ex, p} x  -- elim
>   (:?)  :: Tm {In, TT} x -> Tm {In, TT} x -> Tm {Ex, TT} x      -- typing

|Scope| represents bodies of binders, but the representation differs
with phase. In \emph{terms}, |x :. t| is a \emph{binder}: the |t| is a
de Bruijn term with a new bound variable 0, and the old ones
incremented. The |x| is just advice for display-name selection.  In
values, computation halts at a binder: we store the environment which
awaits an entry for the bound variable to support the evaluation of
the stored term.

> data Scope :: {Phase} -> * -> * where
>   (:.)  :: String -> Tm {In, TT} x           -> Scope {TT} x  -- binding
>   H     :: ENV -> String -> Tm {In, TT} x    -> Scope {VV} x  -- closure
>   K     :: Tm {In, p} x                      -> Scope p x     -- constant

The |Can| functor explains how canonical objects are constructed from
subobjects (terms or values, as appropriate). Lambda is not included here:
morally, it belongs; practically, adapting |Can| to support binding
complicates the definition.

> data Can :: * -> * where
>   Set   :: Can t                                   -- set of sets
>   Pi    :: t -> t -> Can t                         -- functions
>   Con   :: t -> Can t
>   import <- CanConstructors
>   deriving (Show, Eq)

The |Elim| functor explains how eliminators are constructed from their
subobjects. It's a sort of logarithm. Projective eliminators for types
with \(\eta\)-laws go here.

> data Elim :: * -> * where
>   A     :: t -> Elim t                             -- application
>   import <- ElimConstructors
>   deriving (Show, Eq)

Other computation is performed by a fixed repertoire of operators. To
construct an operator, you need a name (for scope resolution and
printing), an arity (so the resolver can manage fully applied usage),
a typing rule, and a computation strategy. The |opTy| field explains
how to label the operator's arguments with the types they must have
and delivers the type of the whole applications: to do that, one must
be able to evaluate arguments. It is vital to check the subterms (left
to right) before trusting the type at the end.

> data Op = Op
>   { opName  :: String, opArity :: Int
>   , opTy    :: forall t. (t -> VAL) -> [t] -> Maybe ([TY :>: t] , TY)
>   , opRun   :: [VAL] -> Either NEU VAL
>   }

Meanwhile, the |opRun| argument implements the computational
behaviour: given suitable arguments, we should receive a value, or
failing that, the neutral term to blame for the failure of
computation. For example, if `append' were an operator, it would
compute if the first list is nil or cons, but complain about the first
list if it is neutral.


\subsection{Useful Abbreviations}

We have some pattern synonyms for common, er, patterns.

> pattern SET       = C Set                   -- set of sets
> pattern Arr s t   = C (Pi s (L (K t)))      -- simple arrow
> pattern PI x s t  = C (Pi s (L (x :. t)))   -- dependent functions
> pattern CON t     = C (Con t)
> pattern NV n      = N (V n)
> import <- CanPats

We have some type synonyms for commonly occurring instances of |Tm|.

> type InTm   = Tm {In, TT}
> type ExTm   = Tm {Ex, TT}
> type INTM   = InTm REF
> type EXTM   = ExTm REF
> type VAL    = Tm {In, VV} REF
> type TY     = VAL
> type NEU    = Tm {Ex, VV} REF
> type ENV    = Bwd VAL

We have special pairs for types going into and coming out of stuff.

> data y :>: t = y :>: t  deriving (Show,Eq)
> infix 4 :>:
> data t :<: y = t :<: y  deriving (Show,Eq)
> infix 4 :<:

\subsection{Syntactic Equality}

We use syntactic equality on \(\eta\)-quoted values to implement the
definitional equality. For terms, it's mainly structural.

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

For scopes, we should only ever see full binders, and we compare them
ignoring name advice: de Bruijn indexing gets rid of \(\alpha\)-conversion
issues.

> instance Eq x => Eq (Scope {TT} x) where
>   (_ :. t0)  == (_ :. t1)  = t0 == t1
>   K t0       == _          = error "unexpected K"
>   _          == K t1       = error "unexpected K"
>   _          == _          = False

Operators are compared by name!

> instance Eq Op where
>   op0 == op1 = opName op0 == opName op1

We provide a smashing operator, for things whose precise values are
irrelevant. We intend this for proofs, but there may be other things
(like name advice) for which we should use it.

> data Irr x = Irr x deriving Show
> instance Eq (Irr x) where
>   _ == _ = True

\subsection{References}

References are the key way we represent free variables, declared,
defined, and deluded. References carry not only names, but types and
values, and are shared.

> data REF = Name := (RKind :<: TY) deriving Show -- is shared where possible
> infix 2 :=
>
> type Name = [(String, Int)]
>
> -- |instance Show REF where|
> --   |show (n := _) = show n|
>
> instance Eq REF where
>   (x := _) == (y := _) = x == y  -- could use cheeky pointer equality?

> data RKind
>   =  DECL
>   |  DEFN VAL
>   |  HOLE
>   deriving Show

> pval :: REF -> VAL
> pval (_ := DEFN v :<: _)  = v
> pval r                      = N (P r)

> pty :: REF -> VAL
> pty (_ := _ :<: ty) = ty


\subsection{Computation}

> ($$) :: VAL -> Elim VAL -> VAL
> L (K v)      $$ A _  = v
> L (H g _ t)  $$ A v  = eval t (g :< v)
> import <- ElimComputation
> N n          $$ e    = N (n :$ e)

> (@@) :: Op -> [VAL] -> VAL
> op @@ vs = either (\_ -> N (op :@ vs)) id (opRun op vs) 

> body :: Scope {TT} REF -> ENV -> Scope {VV} REF
> body (K v)     g = K (eval v g)
> body (x :. t)  g = H g x t

> eval :: Tm {d, TT} REF -> ENV -> VAL
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


\subsection{Variable Manipulation}

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

> (%%) :: Mangle I x y -> Tm {In, TT} x -> Tm {In, TT} y
> m %% t = unI $ m % t

%format $:$ = "\mathbin{\$\!:\!\$}"

> type Spine p x = [Elim (Tm {In, p} x)]
> ($:$) :: Tm {Ex, p} x -> Spine p x -> Tm {Ex, p} x
> ($:$) = foldl (:$)

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
> underScope (_ :. t)  x = under 0 x %% t

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
>   traverse f (Con t)   = (|Con (f t)|)
>   import <- TraverseCan

> instance HalfZip Can where
>    halfZip Set        Set        = Just Set
>    halfZip (Pi s1 t1) (Pi s2 t2) = Just $ Pi (s1,s2) (t1,t2)
>    halfZip (Con t1)   (Con t2)   = Just $ Con (t1,t2)
>    import <- HalfZipCan
>    halfZip _          _          = Nothing

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


> instance Functor (Scope {TT}) where
>   fmap = fmapDefault
> instance Foldable (Scope {TT}) where
>   foldMap = foldMapDefault
> instance Traversable (Scope {TT}) where
>   traverse f (x :. t)   = (|(x :.) (traverse f t)|)
>   traverse f (K t)      = (|K (traverse f t)|)


> instance Functor (Tm {d,TT}) where
>   fmap = fmapDefault
> instance Foldable (Tm {d,TT}) where
>   foldMap = foldMapDefault
> instance Traversable (Tm {d,TT}) where
>   traverse f (L sc)     = (|L (traverse f sc)|)
>   traverse f (C c)      = (|C (traverse (traverse f) c)|)
>   traverse f (N n)      = (|N (traverse f n)|)
>   traverse f (P x)      = (|P (f x)|)
>   traverse f (V i)      = pure (V i)
>   traverse f (t :$ u)   = (|(:$) (traverse f t) (traverse (traverse f) u)|)
>   traverse f (op :@ ts) = (|(op :@) (traverse (traverse f) ts)|)
>   traverse f (tm :? ty) = (|(:?) (traverse f tm) (traverse f ty)|)

> traverseScVal :: (Applicative f) => (REF -> f REF) -> 
>                                     Scope {VV} REF ->
>                                     f (Scope {VV} REF)
> traverseScVal f (H vs x t) = 
>     (|H (traverse (traverseVal f) vs) ~x (traverse f t)|)
> traverseScVal f (K t)      = (|K (traverseVal f t)|)

> traverseVal :: (Applicative f) => (REF -> f REF) -> Tm {d,VV} REF -> f VAL
> traverseVal f (L sc)     = (|L (traverseScVal f sc)|)
> traverseVal f (C c)      = (|C (traverse (traverseVal f) c)|)
> traverseVal f (N n)      = traverseVal f n
> traverseVal f (P x)      = (|pval (f x)|)
> traverseVal f (t :$ u)   = 
>   (|($$) (traverseVal f t) (traverse (traverseVal f) u)|)
> traverseVal f (op :@ ts) = (|(op @@) (traverse (traverseVal f) ts)|)

%endif
