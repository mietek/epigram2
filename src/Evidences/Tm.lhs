
\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable,
>     FunctionalDependencies, UndecidableInstances #-}

> module Evidences.Tm where

> import Prelude hiding (foldl, exp)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Writer
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

> data Part :: * where
>   Head :: Part
>   Body :: Part
>   deriving SheSingleton

> data Status :: * where
>   Val :: Status
>   Exp :: Status
>   deriving (SheSingleton, Show)

> data Tm :: {Part, Status, Nat} -> * where
>   L     :: Env {n} {m} -> String -> Tm {Body, Exp, S m}   -> Tm {Body, s, n}
>   LK    :: Tm {Body, Exp, n}                              -> Tm {Body, s, n}
>   (:-)  :: Can -> [Tm {Body, Exp, n}]                     -> Tm {Body, s, n}
>   (:$)  :: Tm {Head, s, n} -> Bwd (Elim (Tm {Body, Exp, n}))
>                                                           -> Tm {Body, s, n}
>   D     :: {: p :: Part :} => DEF -> Stk EXP -> Operator {p, s}    
>                                                           -> Tm {p, s,  n}
>
>   V     :: Fin {n}      {- dB i -}                        -> Tm {Head, s,  n}
>   P     :: (Int, String, TY)    {- dB l -}                -> Tm {Head, s,  n}
>
>   (:/)  :: {: p :: Part :} => Env {n} {m} -> Tm {p, s, m}  -> Tm {p', Exp, n}

> data Operator :: {Part, Status} -> * where
>   Eat    :: Operator {p, s} -> Operator {Body, s'}
>   Emit   :: Tm {Body, Exp, Z} -> Operator {Body, Exp}
>   Hole   :: Operator {p, s}
>   Case   :: [(Can , Operator {Body, s})] -> Operator {Body, s'}
>   StuckCase  :: [(Can, Operator {Body, s})] -> Operator {Head, s'}
>   Split  :: Operator {p, s} -> Operator {Body, s'}

> type OpMaker s = Int -> Operator {Body,s}

> eat :: String -> ((forall t. Wrapper t {Z} => t) -> OpMaker s') -> OpMaker s
> eat y b p = let x :: Tm {Head, Exp, Z} ; x = P (p,y,undefined) 
>             in  Eat (b (wrapper x B0) (p + 1))

> emit :: Tm {Body, Exp, Z} -> OpMaker {Exp}
> emit x _ = Emit x

> split :: OpMaker s -> OpMaker s'
> split o i = Split (o i)

> cases :: [(Can , OpMaker s)] -> OpMaker s'
> cases ps i = Case $ map (\(c,om) -> (c,om i)) ps

> mkDEF :: Name -> TY -> OpMaker {Exp} -> DEF
> mkDEF nom ty f = DEF
>  { defName = nom
>  , defTy   = ty
>  , defOp   = f 0
>  }

> idDEF :: DEF
> idDEF = mkDEF [("PRIM",0),("id",0)] (("S",SET) ->> \_S -> _S --> _S) $
>  eat "S" $ \ _S -> eat "s" $ \ s -> emit s

> uncurryDEF :: DEF
> uncurryDEF = mkDEF 
>   [("PRIM",0),("uncurry",0)]
>   (("S",SET) ->> \_S -> 
>    ("T",_S --> SET) ->> \_T -> 
>    ("C",SET) ->> \_C -> 
>    (("x",_S) ->> \ x -> _T x --> _C) --> 
>    (("x",_S) -** \ x -> _T x) --> _C) $
>   eat "S" $ \ _S -> eat "T" $ \ _T -> eat "C" $ \ _C -> 
>     eat "f" $ \ f -> split $ eat "s" $ \ s -> eat "t" $ \ t ->
>     emit (f s t)

> zeroElimDEF :: DEF
> zeroElimDEF = mkDEF
>   [("PRIM",0),("zeroElim",0)]
>   (ZERO --> (("S",SET) ->> \_S -> _S))
>   (cases [])

> inhElimDEF :: DEF
> inhElimDEF = mkDEF
>   [("PRIM",0),("inhElim",0)]
>   (("T",SET) ->> \_T ->
>    ("p",PRF (INH _T)) ->> \p ->
>    ("P",PRF (INH _T) --> PROP) ->> \_P ->
>    ("m",(("t",_T) ->> \t -> PRF (_P (WIT t)))) ->> \m ->
>    PRF (_P p)) $
>   eat "T" $ \_T ->
>    cases [(Wit , eat "t" $ \t -> eat "P" $ \_P -> eat "m" $ \m -> 
>             emit (m t))]
>    
> prims :: [ DEF ] 
> prims = [ idDEF , uncurryDEF , zeroElimDEF , inhElimDEF ]

> eats :: Int -> Operator {Body, s} -> Operator {Body, s}
> eats 0 o = o
> eats n o = Eat (eats (n-1) o) 

> instance Show (Operator {p, s}) where
>   show o = "oooo"

> data Stk x  =  S0
>             |  Stk x :<!: x
>             |  SSplit (Stk x)
>             |  SCase Can Int (Stk x)
>   deriving (Eq, Functor, Foldable, Traversable)

> instance HalfZip Stk where
>   halfZip S0 S0 = (| S0 |)
>   halfZip (s :<!: x) (t :<!: y) = (| halfZip s t :<!: ~(x,y) |)
>   halfZip (SSplit s) (SSplit t) = (| SSplit (halfZip s t) |)
>   halfZip (SCase c i s) (SCase d j t) | c == d && i == j = (| SCase ~c ~i (halfZip s t) |)
>   halfZip _ _ = (|)

> rewindStk :: Stk EXP -> [EXP] -> [EXP]
> rewindStk S0 es                  = es
> rewindStk (s :<!: e) es          = rewindStk s (e:es)
> rewindStk (SSplit s) (e1:e2:es)  = rewindStk s (PAIR e1 e2 : es)
> rewindStk (SCase c i s) es    = rewindStk s ((c :- es1) : es2)
>   where (es1, es2) = splitAt i es


-- Why not make the first component an array?

> type Env n m = (Maybe [Tm {Body, Exp, n}], IEnv {n, m})

> data IEnv :: {Nat, Nat} -> * where
>  INix   :: IEnv {n, Z}
>  INil   :: IEnv {n, n}
>  (:<<:)  :: IEnv {m, n} -> Tm {Body, s, Z} -> IEnv {m, S n} 


> (!.!) :: IEnv {Z, n} -> Fin {n} -> Tm {Body, Exp, Z}
> (ez :<<: e) !.! Fz = exp e 
> (ez :<<: e) !.! Fs i = ez !.! i

> (<:<) :: Env {m} {n} -> EXP -> Env {m} {S n}
> (gl, gi) <:< e = (gl, gi :<<: e)

> (<+<) :: Env {m} {n} -> Env {n} {o} -> Env {m} {o}
> (gl, gi) <+< (gl', gi') = (gln, gi <<< gi')
>   where 
>    (<<<) :: forall m n o. IEnv {m, n} -> IEnv {n, o} -> IEnv {m, o}
>    g <<< INix = INix
>    g <<< INil = g
>    g <<< (g' :<<: e) = (g <<< g') :<<: e
>    gln = case (gl, gl') of
>     (_, Just y) -> Just (map ((gl, gi) :/) y)
>     (Just x, _) -> Just x
>     _           -> Nothing

> pattern ENil = (Nothing, INil)
> pattern ENix = (Nothing, INix)

> data DEF = DEF  {  defName :: Name
>                 ,  defTy :: TY
>                 ,  defOp :: Operator {Body, Exp}
>                 }
>   deriving Show

> instance Eq DEF where
>   d1 == d2 = defName d1 == defName d2

> type EXP = Tm {Body, Exp, Z}
> type VAL = Tm {Body, Val, Z}
> type TY = EXP

> data Elim :: * -> * where
>   A  :: t -> Elim t
>   Hd :: Elim t
>   Tl :: Elim t
>   Out :: Elim t
>   deriving (Show, Eq, Foldable, Traversable, Functor)

> data Can :: * where
>   Set    :: Can                            -- set of sets
>   Pi     :: Can                            -- functions
>   Sigma  :: Can                            -- products 
>   Pair   :: Can                            -- pairs
>   Con    :: Can                            -- general purpose constructor
>   One    :: Can                            -- things that have a certain one-ness
>   Zero   :: Can                            -- things that have a certain zero-ness
>   -- [Feature = Prop]
>   Prop   :: Can                            -- set of props
>   Prf    :: Can                            -- set of proofs of a prop
>   Inh    :: Can                            -- set inhabitation prop
>   Wit    :: Can                            -- witness to inhabitation 
>   And    :: Can                            -- prop conj
>   Chkd   :: Can                            -- content of a proof after type checking
>   -- [/Feature = Prop]
>   -- [Feature = Eq]
>   Eq     :: Can                            -- equality type
>   -- [/Feature = Eq]
>   deriving (Eq, Show)

> pattern SET        = Set :- []             
> pattern ARR s t    = Pi :- [s, (LK t)]     
> pattern PI s t     = Pi :- [s, t]          
> pattern TIMES s t  = Sigma :- [s, (LK t)]  
> pattern SIGMA s t  = Sigma :- [s, t]      
> pattern PAIR a b   = Pair :- [a, b]      
> pattern CON t      = Con :- [t]         
> pattern ONE        = One :- []
> pattern ZERO       = Zero :- []
>   -- [Feature = Prop]
> pattern PROP       = Prop :- []
> pattern PRF _P     = Prf :- [_P]
> pattern INH _T     = Inh :- [_T]
> pattern WIT t      = Wit :- [t]
> pattern AND _P _Q  = And :- [_P,_Q]
> pattern ALL _S _P  = Pi :- [_S, _P]
> pattern CHKD       = Chkd :- []
>   -- [/Feature = Prop]

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
 
> eval :: forall m n p s' . pi (s :: Status) . 
>           Env {Z} {n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> eval {s} g (L g' x b) = L (g <+< g') x b
> eval {s} g (LK e) = LK (g :/ e)
> eval {s} g (c :- es) = c :- (fmap (g :/) es)
> eval {s} g (h :$ es) = applys {s} (eval {s} g h) (fmap (fmap (g :/)) es)
> eval {s} (Nothing, _) (D d ez o) = mkD {s} d ez o
> eval {s} (Just es, _) (D d ez o) = mkD {s} d (fmap ((Just es, INix) :/) ez) o
> eval {s} (es, ez) (V i) = eval {s} ENil (ez !.! i)
> eval {s} (Nothing, _) (P lt) = P lt :$ B0
> eval {s} (Just es, _) (P (l, _, _)) = eval {s} ENil (es !! l)
> eval {s} g (g' :/ e) = eval {s} (g <+< g') e

> (//) :: {:s :: Status:} => Env {Z} {n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> (//) = eval {:s :: Status:}

> apply :: forall s' . pi (s :: Status) . 
>          Tm {Body, s, Z} -> Elim (Tm {Body, s', Z}) -> Tm {Body, s, Z} 
> apply {s} (L (gl, gi) _ b) (A a) = eval {s} (gl, gi :<<: a) b 
> apply {s} (LK e) _ = eval {s} ENil e
> apply {s} (D d es (Eat o)) (A a) = mkD {s} d (es :<!: exp a) o  
> apply {Val} (D d es (Case os)) (A a) = 
>   case (ENil // a :: VAL) of -- check that it's canonical
>     (c :- as) -> case lookup c os of
>       (Just o) -> foldl ($$.) (mkD {Val} d es o) as
>       Nothing -> error "You muppet"             
>     x -> D d (es :<!: exp x) (StuckCase os) :$ B0
> apply {Val} (D d es (Split o)) (A a) = 
>   mkD {Val} d es o $$. ((ENil :/ a) :$ (B0 :< Hd)) $$. ((ENil :/ a) :$ (B0 :< Tl))
> apply {Exp} d@(D _ _ _) a = (ENil :/ d) :$ (B0 :< fmap exp a)  
> apply {s} (PAIR a b) Hd = eval {s} ENil a
> apply {s} (PAIR a b) Tl = eval {s} ENil b
> apply {s} (h :$ ss) a = h :$ (ss :< fmap exp a)
> apply {Exp} (g :/ t) a = (g :/ t) :$ (B0 :< fmap exp a)

> ($$) :: {:s :: Status:} => 
>         Tm {Body, s, Z} -> Elim (Tm {Body, s', Z}) -> Tm {Body, s, Z}
> ($$) = apply {:s :: Status:}

> ($$.) :: {:s :: Status:} => 
>         Tm {Body, s, Z} -> Tm {Body, s', Z} -> Tm {Body, s, Z}
> f $$. a = f $$ A a 

> applys :: pi (s :: Status) . 
>           Tm {Body, s, Z} -> Bwd (Elim EXP) -> Tm {Body, s, Z}
> applys {s} v B0 = v
> applys {s} v (ez :< e) = apply {s} (applys {s} v ez) e

> ($$$) :: {:s :: Status:} => 
>          Tm {Body, s, Z} -> Bwd (Elim EXP) -> Tm {Body, s, Z}
> ($$$) = applys {:s :: Status:}

> ($$$.) :: {:s :: Status:} => 
>          Tm {Body, s, Z} -> Bwd EXP -> Tm {Body, s, Z}
> f $$$. as = f $$$ fmap A as

> mkD :: forall s' p . pi (s :: Status) . 
>        DEF -> Stk EXP -> Operator {p, s'} -> Tm {Body, s, Z}
> mkD {s} d es (Emit t)               = eval {s} (Just (trail es), INix) t
> mkD {s} d es (Eat o)                = D d es (Eat o)
> mkD {s} d es Hole                   = D d es Hole :$ B0
> mkD {s} d es (Case os)              = D d es (Case os) 
> mkD {s} d es (Split o)              = D d es (Split o) 
> mkD {s} d (es :<!: e) (StuckCase os)  = apply {s} (D d es (Case os)) (A e)

> fortran :: String -> [Tm {Body, Val, n}] -> Tm {Body, Val, n} -> String
> fortran _ (L _ s _:_) _ = s
> fortran s (_:x) y = fortran s x y
> fortran s [] _ = s

> wk :: {: p :: Part :} => Tm {p, s, Z} -> Tm {p', Exp, n}
> wk t = (Nothing, INix) :/ t

> (***) = TIMES
> (-->) = ARR
> (==>) = ARR . PRF
> infixr 5 ==>, -->, ***


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

\paragraph{Kinds of Parameters:}

A \emph{parameter} is either a $\lambda$, $\forall$ or $\Pi$
abstraction. It scopes over all following entries and the definitions
(if any) in the enclosing development.

> data ParamKind = ParamLam | ParamAll | ParamPi
>       deriving (Show, Eq)


The link between a type and the kind of parameter allowed is defined
by |lambdable|:

> lambdable :: VAL -> Maybe (ParamKind, TY, Tm {Body, s, Z} -> TY)
> lambdable (PI s t)         = Just (ParamLam, s, (t $$.))
> lambdable (PRF _P) = case ev _P of
>   (PI s p)  -> Just (ParamAll, s, \v -> PRF (p $$ A v))
>   _         -> (|)
> lambdable _                = Nothing

> projable :: VAL -> Maybe (TY, Tm {Body, s, Z} -> TY)
> projable (SIGMA s t)         = Just (s, (t $$.))
> projable (PRF _P) = case ev _P of
>   (AND _P _Q)  -> Just (PRF _P, \_ -> PRF _Q)
>   _            -> (|)
> projable _                = Nothing


> bod :: forall s n. pi (p :: Part). Tm {p, s, n} -> Tm {Body, s, n}
> bod {Body} = id
> bod {Head} = (:$ B0)

> toBody :: {: p :: Part :} => Tm {p, s, n} -> Tm {Body, s, n}
> toBody = bod {:p :: Part :}

> class Wrapper (t :: *) (n :: {Nat}) | t -> n where
>   wrapper :: Tm {Head, Exp, n} -> Bwd (Tm {Body, Exp, n}) -> t

> instance Wrapper (Tm {Body, Exp, n}) n where
>   wrapper h es = h :$ fmap A es

> instance (s ~ Tm {Body, Exp, n}, Wrapper t n) => Wrapper (s -> t) n where
>   wrapper f es e = wrapper f (es :< e) 

> wr :: Wrapper t {n} => EXP -> t
> wr e = wrapper (wk e) B0

 instance (Wrapper s n, Wrapper t n) => Wrapper (s, t) n where
   wrapper f es = (wrapper f es, wrapper f es)

> cough :: (Fin {S m} -> Tm {p, b, m}) -> Tm {p, b, m}
> cough f = f Fz  -- coughs up the zero you want

> la ::  String ->
>        ((forall t n. (Wrapper t n, Leq {S m} n) => t)
>          -> Tm {Body, Exp, S m}) ->
>        Tm {Body, s, m}
> la s b = cough $ \ fz -> L ENil s (b (wrapper (V (finj fz)) B0))

> (->>) :: (String, Tm {Body, Exp, m}) ->
>          ((forall t n. (Wrapper t n, Leq {S m} n) => t)
>            -> Tm {Body, Exp, S m}) ->
>        Tm {Body, s, m}
> (x, s) ->> t = PI s (la x t)

> (-**) :: (String, Tm {Body, Exp, m}) ->
>          ((forall t n. (Wrapper t n, Leq {S m} n) => t)
>            -> Tm {Body, Exp, S m}) ->
>        Tm {Body, s, m}
> (x, s) -** t = SIGMA s (la x t)

> ugly :: Vec {n} String -> Tm {p, s, n} -> String
> ugly xs (L ENil x b) = "(\\ " ++ x ++ " -> " ++ ugly (x :>>: xs) b ++ ")"
> ugly xs (L _    x b)  = "(\\ " ++ x ++ " -> ???)"
> ugly xs (LK e)       = "(\\ _ -> " ++ ugly xs e ++ ")"
> ugly xs (ARR s t) = "(" ++ ugly xs s ++ " -> " ++ ugly xs t ++ ")"
> ugly xs (PI s (L ENil x t)) = "((" ++ x ++ " : " ++ ugly xs s ++ ") -> "
>                              ++ ugly (x :>>: xs) t ++ ")"
> ugly xs (PI s (L _    x t)) = "((" ++ x ++ " : " ++ ugly xs s ++ ") -> ???)"
> ugly xs (TIMES s t) = "(" ++ ugly xs s ++ " * " ++ ugly xs t ++ ")"
> ugly xs (SIGMA s (L ENil x t)) = "((" ++ x ++ " : " ++ ugly xs s ++ ") * "
>                              ++ ugly (x :>>: xs) t ++ ")"
> ugly xs (SIGMA s (L _    x t)) = "((" ++ x ++ " : " ++ ugly xs s ++ ") * ??? )"
> ugly xs (c :- []) = show c
> ugly xs (c :- es) = "(" ++ show c ++ foldMap (\ e -> " " ++ ugly xs e) es ++ ")"
> ugly xs (h :$ B0) = ugly xs h
> ugly xs (h :$ es) = "(" ++ ugly xs h ++ foldMap (\ e -> " " ++ uglyElim xs e) es ++ ")"
> ugly xs (V i) = xs !>! i
> ugly xs (P (i, s, t)) = s
> ugly xs (D d S0 _) = "DEF: " ++ show (defName d)
> ugly xs (D d es _) = "(" ++ show (defName d) ++ foldMap (\ e -> " " ++ ugly V0 e) (rewindStk es []) ++ ")"
> ugly xs (ENil :/ e) = ugly xs e
> ugly _ _ = "???"

> uglyElim :: Vec {n} String -> Elim (Tm {p, s, n}) -> String
> uglyElim v (A e) = ugly v e
> uglyElim v Hd = "!"
> uglyElim v Tl = "-"
> uglyElim v Out = "%"

> instance {:n :: Nat:} => Show (Tm {p, s, n}) where
>   show t = ugly (fmap (\ i -> "v" ++ show i) vUpTo') t

Pos could use a nice abstraction to do the following:

> capture :: pi (m :: Nat). EXP -> Tm {Body, Exp, m}
> capture {m} t = (Just (Data.Foldable.foldr (\i l -> (V i :$ B0) : l) [] (vDownFromF {m})) , INix) :/ t

> capture' :: {: m :: Nat :} =>  EXP -> Tm {Body, Exp, m}
> capture' = capture {: m :: Nat :} 

> piLift :: pi (n :: Nat). Vec {n} (String, TY) -> TY -> TY
> piLift {n} bs t = pil bs (capture {n} t) 
>   where
>     pil :: Vec {m} (String, TY) -> Tm {Body, Exp, m} -> EXP
>     pil V0 t = t
>     pil ((s,ty) :>>: sts) t = pil sts $ PI (wk ty) (L ENil s t)

> piLift' :: {: n :: Nat :} => Vec {n} (String, TY) -> TY -> TY
> piLift' = piLift {: n :: Nat :}

