
\section{NewTm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables #-}

> module Evidences.NewTm where

> import Prelude hiding (foldl, exp)

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

> data Status = Val | Exp

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

> (//) :: Env {Z, n} -> Tm {p, s, n} -> VAL
> g // L g' x b = L (g <+< g') x b 
> g // LK e = LK (g :/ e)
> g // (c :- es) = c :- (fmap (g :/) es)
> g // (h :$ es) = (g // h) $$$ fmap (g :/) es
> (Nothing, _) // D d ez o = valD d ez o
> (Just es, _) // D d ez o = valD d (fmap ((Just es, INix) :/) ez) o
> (es, ez) // V i = ENil // (ez !.! i)
> (Just es, _) // P (l, _) = ENil // (es !! l)
> (Nothing, _) // P lt = P lt :$ B0
> g // (g' :/ e) = (g <+< g') // e

> ($$) :: VAL -> Tm {Body, s, Z} -> VAL
> L (gl, gi) _ b $$ a = (gl, gi :<: a) // b 
> LK e $$ _ = ENil // e
> D d es (Eat o) $$ a = valD d (es :< exp a) o  
> D d es (Case os) $$ a = 
>   case ENil // a of
>     (c :- as) -> case lookup c os of
>       (Just o) -> foldl ($$) (valD d es o) as
>       Nothing -> error "You muppet"             
>     x -> D d (es :< exp x) (StuckCase os) :$ B0
> D d es (Split o) $$ a = 
>   valD d es o $$ (exp a :$ (B0 :< HD)) $$ (exp a :$ (B0 :< TL))
> PAIR a b $$ HD = ENil // a
> PAIR a b $$ TL = ENil // b

> ($$$) :: VAL -> Bwd EXP -> VAL
> v $$$ B0 = v
> v $$$ (ez :< e) = (v $$$ ez) $$ e

> valD :: DEF -> Bwd EXP -> Operator {p, s} -> VAL
> valD d es (Emit t)               = (Just (trail es), INix) // t
> valD d es (Eat o)                = D d es (Eat o)
> valD d es Hole                   = D d es Hole :$ B0
> valD d es (Case os)              = D d es (Case os) 
> valD d (es :< e) (StuckCase os)  = D d es (Case os) $$ e

> ($?) :: EXP -> EXP -> EXP
> L (gl, gi) _ b $? a = (gl, gi :<: a) /? b 
> LK e $? _ = (Nothing, INil) /? e
> D d es (Eat o) $? a = expD d (es :< a) o 
> d@(D _ _ _) $? a = (ENil :/ d) :$ (B0 :< a)  

> ($?$) :: EXP -> Bwd EXP -> EXP
> v $?$ B0 = v
> v $?$ (ez :< e) = (v $?$ ez) $? e

> (/?) :: Env {Z, n} -> Tm {p, s, n} -> EXP
> g /? L g' x b = L (g <+< g') x b 
> g /? LK e = LK (g :/ e)
> g /? (c :- es) = c :- (fmap (g :/) es)
> g /? (h :$ es) = (g /? h) $?$ fmap (g :/) es
> (Nothing, _) /? D d ez o = expD d ez o
> (Just es, _) /? D d ez o = expD d (fmap ((Just es, INix) :/) ez) o
> (es, ez) /? V i = ENil /? (ez !.! i)
> (Nothing, _) /? P lt = P lt :$ B0
> (Just es, _) /? P (l, _) = ENil /? (es !! l)
> g /? (g' :/ e) = (g <+< g') /? e

> expD :: DEF -> Bwd EXP -> Operator {p, s} -> EXP
> expD d es (Emit t)  = D d es (Emit t)
> expD d es (Eat o)   = D d es (Eat o) 
> expD d es Hole      = D d es Hole :$ B0
> expD d es (Case os)              = D d es (Case os) 
> expD d (es :< e) (StuckCase os)  = D d es (Case os) $? e
