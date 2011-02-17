
\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}

> module Evidences.Tm where

> import Prelude hiding (foldl, exp)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import qualified Data.Monoid as M
> import Data.Foldable
> import Data.List hiding (foldl)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Unsafe.Coerce

%endif


> type Name = [(String, Int)]

> data Part = Head | Body

> data Status :: * where
>   Val :: Status
>   Exp :: Status
>   deriving SheSingleton

> data Tm :: {Part, Status, Nat} -> * where
>   L     :: Env {n, m} -> String -> Tm {Body, Exp, S m}   -> Tm {Body, s, n}
>   LK    :: Tm {Body, Exp, n}                             -> Tm {Body, s, n}
>   (:-)  :: Can -> [Tm {Body, Exp, n}]                    -> Tm {Body, s, n}
>   (:$)  :: Tm {Head, s, n} -> Bwd (Tm {Body, Exp, n})  -> Tm {Body, s, n}
>   D     :: DEF -> Bwd EXP -> Operator {p, s}             -> Tm {p, s,  n}
>
>   V     :: Fin {n}      {- dB i -}                       -> Tm {Head, s,  n}
>   P     :: (Int, String, TY)    {- dB l -}                       -> Tm {Head, s,  n}
>
>   (:/)  :: Env {n, m} -> Tm {p, s, m}                  -> Tm {p', Exp, n}

> data Operator :: {Part, Status} -> * where
>   Eat    :: Operator {p, s} -> Operator {Body, s'}
>   Emit   :: Tm {Body, Exp, Z} -> Operator {Body, Exp}
>   Hole   :: Operator {Head, s}
>   Case   :: [(Can , Operator {Body, s})] -> Operator {Body, s'}
>   StuckCase  :: [(Can, Operator {Body, s})] -> Operator {Head, s'}
>   Split  :: Operator {p, s} -> Operator {Body, s'}

-- Why not make the first component an array?

> type Env nm = (Maybe [EXP], IEnv nm)

> data IEnv :: {Nat, Nat} -> * where
>  INix   :: IEnv {n, Z}
>  INil   :: IEnv {n, n}
>  (:<<:)  :: IEnv {m, n} -> Tm {Body, s, Z} -> IEnv {m, S n} 

> exp :: Tm {p, s, n} -> Tm {p, Exp, n}
> exp = unsafeCoerce
> {-
> exp (L a b c) = L a b c
> exp (LK a) = LK a
> exp (a :- b) = a :- b
> exp (a :$ b) = exp a :$ b
> exp (V i) = V i
> exp (P l) = P l
> exp (a :/ b) = a :/ b
> exp (D a b c) = D a b (expo c)
>  where expo :: Operator {p, s} -> Operator {p, Exp}
>        expo (Eat o) = Eat o
>        expo (Emit t) = Emit t
>        expo Hole = Hole
>        expo (Case os) = Case os
>        expo (StuckCase os) = StuckCase os
>        expo (Split o) = Split o
> -}

> ev :: Tm {p, Exp, Z} -> VAL
> ev = (ENil //) 

> (!.!) :: IEnv {Z, n} -> Fin {n} -> Tm {Body, Exp, Z}
> (ez :<<: e) !.! Fz = exp e 
> (ez :<<: e) !.! Fs i = ez !.! i

> (<:<) :: Env {m, n} -> EXP -> Env {m, S n}
> (gl, gi) <:< e = (gl, gi :<<: e)

> (<+<) :: Env {m, n} -> Env {n, o} -> Env {m, o}
> (gl, gi) <+< (gl', gi') = (gln, gi <<< gi')
>   where 
>    (<<<) :: forall m n o. IEnv {m, n} -> IEnv {n, o} -> IEnv {m, o}
>    g <<< INix = INix
>    g <<< INil = g
>    g <<< (g' :<<: e) = (g <<< g') :<<: e
>    gln = case (gl, gl') of
>     (_, Just y) -> Just y
>     (Just x, _) -> Just x
>     _           -> Nothing

> pattern ENil = (Nothing, INil)

> type DEF = (String, TY, Operator {Body, Exp})

> type EXP = Tm {Body, Exp, Z}
> type VAL = Tm {Body, Val, Z}
> type TY = EXP

> data Can :: * where
>   Set    :: Can                            -- set of sets
>   Pi     :: Can                            -- functions
>   Sigma  :: Can                            -- products 
>   Pair   :: Can                            -- pairs
>   Con    :: Can                            -- packing
>   One    :: Can
>   Zero   :: Can
>   deriving (Eq, Show)

> pattern SET        = Set :- []             -- set of sets
> pattern ARR s t    = Pi :- [s, (LK t)]     -- simple arrow
> pattern PI s t     = Pi :- [s, t]          -- dependent functions
> pattern TIMES s t  = Sigma :- [s, (LK t)]  -- simple arrow
> pattern SIGMA s t  = Sigma :- [s, t]       -- dependent product
> pattern PAIR a b   = Pair :- [a, b]        -- pairing
> pattern CON t      = Con :- [t]            -- Container (packing "stuff")
> pattern ONE        = One :- []
> pattern ZERO       = Zero :- []

> eval :: forall m n p s' . pi (s :: Status) . 
>           Env {Z, n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> eval {s} g (L g' x b) = L (g <+< g') x b
> eval {s} g (LK e) = LK (g :/ e)
> eval {s} g (c :- es) = c :- (fmap (g :/) es)
> eval {s} g (h :$ es) = applys {s} (eval {s} g h) (fmap (g :/) es)
> eval {s} (Nothing, _) (D d ez o) = mkD {s} d ez o
> eval {s} (Just es, _) (D d ez o) = mkD {s} d (fmap ((Just es, INix) :/) ez) o
> eval {s} (es, ez) (V i) = eval {s} ENil (ez !.! i)
> eval {s} (Nothing, _) (P lt) = P lt :$ B0
> eval {s} (Just es, _) (P (l, _, _)) = eval {s} ENil (es !! l)
> eval {s} g (g' :/ e) = eval {s} (g <+< g') e

> (//) :: {:s :: Status:} => Env {Z, n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> (//) = eval {:s :: Status:}

> apply :: forall s' . pi (s :: Status) . 
>          Tm {Body, s, Z} -> Tm {Body, s', Z} -> Tm {Body, s, Z} 
> apply {s} (L (gl, gi) _ b) a = eval {s} (gl, gi :<<: a) b 
> apply {s} (LK e) _ = eval {s} ENil e
> apply {s} (D d es (Eat o)) a = mkD {s} d (es :< exp a) o  
> apply {Val} (D d es (Case os)) a = 
>   case (ENil // a :: VAL) of
>     (c :- as) -> case lookup c os of
>       (Just o) -> foldl ($$) (mkD {Val} d es o) as
>       Nothing -> error "You muppet"             
>     x -> D d (es :< exp x) (StuckCase os) :$ B0
> apply {Val} (D d es (Split o)) a = 
>   mkD {Val} d es o $$ ((ENil :/ a) :$ (B0 :< ZERO)) $$ ((ENil :/ a) :$ (B0 :< ONE))
> apply {Exp} d@(D _ _ _) a = (ENil :/ d) :$ (B0 :< exp a)  
> apply {s} (PAIR a b) ZERO = eval {s} ENil a
> apply {s} (PAIR a b) ONE = eval {s} ENil b
> apply {s} (h :$ ss) a = h :$ (ss :< exp a)
> apply {Exp} (g :/ t) a = (g :/ t) :$ (B0 :< exp a)

> ($$) :: {:s :: Status:} => Tm {Body, s, Z} -> Tm {Body, s', Z} -> Tm {Body, s, Z}
> ($$) = apply {:s :: Status:}

> applys :: pi (s :: Status) . Tm {Body, s, Z} -> Bwd EXP -> Tm {Body, s, Z}
> applys {s} v B0 = v
> applys {s} v (ez :< e) = apply {s} (applys {s} v ez) e

> ($$$) :: {:s :: Status:} => Tm {Body, s, Z} -> Bwd EXP -> Tm {Body, s, Z}
> ($$$) = applys {:s :: Status:}

> mkD :: forall s' p . pi (s :: Status) . 
>        DEF -> Bwd EXP -> Operator {p, s'} -> Tm {Body, s, Z}
> mkD {s} d es (Emit t)               = eval {s} (Just (trail es), INix) t
> mkD {s} d es (Eat o)                = D d es (Eat o)
> mkD {s} d es Hole                   = D d es Hole :$ B0
> mkD {s} d es (Case os)              = D d es (Case os) 
> mkD {s} d (es :< e) (StuckCase os)  = apply {s} (D d es (Case os)) e

> fortran :: String -> Tm {Body, s, n} -> Tm {Body, s, n} -> String
> fortran _ (L _ s _) _ = s
> fortran s _ _ = s

> wk :: Tm {p, s, Z} -> Tm {p', Exp, n}
> wk t = (Nothing, INix) :/ t

> (***) = TIMES


We have special pairs for types going into and coming out of
stuff. We write |typ :>: thing| to say that |typ| accepts the
term |thing|, i.e.\ we can push the |typ| in the |thing|. Conversely, we
write |thing :<: typ| to say that |thing| is of inferred type |typ|, i.e.\
we can pull the type |typ| out of the |thing|. Therefore, we can read
|:>:| as ``accepts'' and |:<:| as ``has inferred type''.

> data ty :>: tm = ty :>: tm  deriving (Show,Eq)
> infix 4 :>:
> data tm :<: ty = tm :<: ty  deriving (Show,Eq)
> infix 4 :<:

> fstIn :: (a :>: b) -> a
> fstIn (x :>: _) = x

> sndIn :: (a :>: b) -> b
> sndIn (_ :>: x) = x

> fstEx :: (a :<: b) -> a
> fstEx (x :<: _) = x

> sndEx :: (a :<: b) -> b
> sndEx (_ :<: x) = x

As we are discussing syntactic sugar, we define the ``reduces to'' symbol:

> data t :=>: v = t :=>: v deriving (Show, Eq)
> infix 5 :=>:

with the associated projections:

> valueOf :: (t :=>: v) -> v
> valueOf (_ :=>: v) = v
>
> termOf :: (t :=>: v) -> t
> termOf (t :=>: _) = t

Intuitively, |t :=>: v| can be read as ``the term |t| reduces to the
value |v|''.

