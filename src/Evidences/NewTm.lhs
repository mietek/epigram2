
\section{NewTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}

> module Evidences.NewTm where

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

> import NameSupply.NameSupply

%endif

> data Nat = Z | S Nat

> data Fin :: {Nat} -> * where
>   Fz :: Fin {S n}
>   Fs :: Fin {n} -> Fin {S n}

> data Part = Head | Body

> data Status :: * where
>   Val :: Status
>   Exp :: Status
>   deriving SheSingleton

> data Tm :: {Part, Status, Nat} -> * where
>   L     :: Env {n, m} -> String -> Tm {Body, s, S m}   -> Tm {Body, s', n}
>   LK    :: Tm {Body, s, n}                             -> Tm {Body, s', n}
>   (:-)  :: Can -> [Tm {Body, s, n}]                -> Tm {Body, s', n}
>   (:$)  :: Tm {Head, s, n} -> Bwd (Tm {Body, Exp, n})  -> Tm {Body, s,  n}
>   D     :: DEF -> Bwd EXP -> Operator {p, s}           -> Tm {p, s,  n}

>   V     :: Fin {n}      {- dB i -}                     -> Tm {Head, s,  n}
>   P     :: (Int, TYPE)  {- dB l -}                     -> Tm {Head, s,  n}

>   (:/)  :: Env {n, m} -> Tm {p, s, m}                  -> Tm {p', Exp, n}

> data Operator :: {Part, Status} -> * where
>   Eat    :: Operator {p, s} -> Operator {Body, s'}
>   Emit   :: Tm {Body, Exp, Z} -> Operator {Body, Exp}
>   Hole   :: Operator {Head, s}
>   Case   :: [(Can , Operator {Body, s})] -> Operator {Body, s'}
>   StuckCase  :: [(Can, Operator {Body, s})] -> Operator {Head, s'}
>   Split  :: Operator {p, s} -> Operator {Body, s'}

> type Env nm = (Maybe [EXP], IEnv nm)

> data IEnv :: {Nat, Nat} -> * where
>  INix   :: IEnv {n, Z}
>  INil   :: IEnv {n, n}
>  (:<:)  :: IEnv {m, n} -> Tm {Body, s, Z} -> IEnv {m, S n} 

> exp :: Tm {p, s, n} -> Tm {p', Exp, n}
> exp = (:/) ENil 

> (!.!) :: IEnv {Z, n} -> Fin {n} -> Tm {Body, Exp, Z}
> (ez :<: e) !.! Fz = exp e 
> (ez :<: e) !.! Fs i = ez !.! i

> (<:<) :: IEnv {m, n} -> IEnv {n, o} -> IEnv {m, o}
> g <:< INix = INix
> g <:< INil = g
> g <:< (g' :<: e) = (g <:< g') :<: e

> (<+<) :: Env {m, n} -> Env {n, o} -> Env {m, o}
> (gl, gi) <+< (gl', gi') = (gln, gi <:< gi')
>   where 
>    gln = case (gl, gl') of
>     (_, Just y) -> Just y
>     (Just x, _) -> Just x
>     _           -> Nothing

> pattern ENil = (Nothing, INil)

> type DEF = (String, TYPE, Operator {Body, Exp})

> type EXP = Tm {Body, Exp, Z}
> type VAL = Tm {Body, Val, Z}
> type TYPE = VAL

> data Can :: * where
>   Set    :: Can                            -- set of sets
>   Pi     :: Can                            -- functions
>   Sigma  :: Can                            -- products 
>   Pair   :: Can                            -- pairs
>   Con    :: Can                            -- packing
>   Hd     :: Can
>   Tl     :: Can
>   deriving Eq

> pattern SET        = Set :- []             -- set of sets
> pattern ARR s t    = Pi :- [s, (LK t)]     -- simple arrow
> pattern PI s t     = Pi :- [s, t]          -- dependent functions
> pattern TIMES s t  = Sigma :- [s, (LK t)]  -- simple arrow
> pattern SIGMA s t  = Sigma :- [s, t]       -- dependent product
> pattern PAIR a b   = Pair :- [a, b]        -- pairing
> pattern CON t      = Con :- [t]            -- Container (packing "stuff")
> pattern HD         = Hd :- []
> pattern TL         = Tl :- []

> eval :: forall n p s' . pi (s :: Status) . 
>           Env {Z, n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> eval {s} g (L g' x b) = L (g <+< g') x b
> eval {s} g (LK e) = LK (g :/ e)
> eval {s} g (c :- es) = c :- (fmap (g :/) es)
> eval {s} g (h :$ es) = applys {s} (eval {s} g h) (fmap (g :/) es)
> eval {s} (Nothing, _) (D d ez o) = mkD {s} d ez o
> eval {s} (Just es, _) (D d ez o) = mkD {s} d (fmap ((Just es, INix) :/) ez) o
> eval {s} (es, ez) (V i) = eval {s} ENil (ez !.! i)
> eval {s} (Nothing, _) (P lt) = P lt :$ B0
> eval {s} (Just es, _) (P (l, _)) = eval {s} ENil (es !! l)
> eval {s} g (g' :/ e) = eval {s} (g <+< g') e

> (//) :: Env {Z, n} -> Tm {p, s, n} -> VAL
> (//) = eval {Val}

> apply :: forall s' . pi (s :: Status) . 
>          Tm {Body, s, Z} -> Tm {Body, s', Z} -> Tm {Body, s, Z} 
> apply {s} (L (gl, gi) _ b) a = eval {s} (gl, gi :<: a) b 
> apply {s} (LK e) _ = eval {s} ENil e
> apply {s} (D d es (Eat o)) a = mkD {s} d (es :< exp a) o  
> apply {Val} (D d es (Case os)) a = 
>   case ENil // a of
>     (c :- as) -> case lookup c os of
>       (Just o) -> foldl ($$) (mkD {Val} d es o) as
>       Nothing -> error "You muppet"             
>     x -> D d (es :< exp x) (StuckCase os) :$ B0
> apply {Val} (D d es (Split o)) a = 
>   mkD {Val} d es o $$ (exp a :$ (B0 :< HD)) $$ (exp a :$ (B0 :< TL))
> apply {Exp} d@(D _ _ _) a = (ENil :/ d) :$ (B0 :< exp a)  
> apply {s} (PAIR a b) HD = eval {s} ENil a
> apply {s} (PAIR a b) TL = eval {s} ENil b

> ($$) :: VAL -> Tm {Body, s, Z} -> VAL
> ($$) = apply {Val}

> applys :: pi (s :: Status) . Tm {Body, s, Z} -> Bwd EXP -> Tm {Body, s, Z}
> applys {s} v B0 = v
> applys {s} v (ez :< e) = apply {s} (applys {s} v ez) e

> ($$$) :: VAL -> Bwd EXP -> VAL
> ($$$) = applys {Val}

> mkD :: forall s' p . pi (s :: Status) . 
>        DEF -> Bwd EXP -> Operator {p, s'} -> Tm {Body, s, Z}
> mkD {s} d es (Emit t)               = eval {s} (Just (trail es), INix) t
> mkD {s} d es (Eat o)                = D d es (Eat o)
> mkD {s} d es Hole                   = D d es Hole :$ B0
> mkD {s} d es (Case os)              = D d es (Case os) 
> mkD {s} d (es :< e) (StuckCase os)  = apply {s} (D d es (Case os)) e

> ($?) :: EXP -> Tm {Body, s, Z} -> EXP
> ($?) = apply {Exp}

> ($?$) :: EXP -> Bwd EXP -> EXP
> ($?$) = applys {Exp}

> (/?) :: Env {Z, n} -> Tm {p, s, n} -> EXP
> (/?) = eval {Exp}

