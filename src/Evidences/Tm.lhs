
\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable,
>     FunctionalDependencies, UndecidableInstances #-}

> module Evidences.Tm where

> import Prelude hiding (foldl, exp, all)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Writer
> import qualified Data.Monoid as M
> import Data.Foldable
> import Data.List hiding (foldl, all)
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
>   L     :: Env {n} {m} -> String -> Tm {Body, Exp, S m}    -> Tm {Body, s, n}
>   LK    :: Tm {Body, Exp, n}                               -> Tm {Body, s, n}
>   (:-)  :: Can -> [Tm {Body, Exp, n}]                      -> Tm {Body, s, n}
>   (:$)  :: Tm {Head, s, n} -> Bwd (Elim (Tm {Body, Exp, n}))
>                                                            -> Tm {Body, s, n}
>   D     :: {: p :: Part :} => DEF -> Stk EXP -> Operator {p, s}    
>                                                            -> Tm {p, s,  n}
>
>   V     :: Fin {n}      {- dB i -}                         -> Tm {Head, s,  n}
>   P     :: (Int, String, TY)    {- dB l -}                 -> Tm {Head, s,  n}
>
>   Refl  :: Tm {Body, Exp, n} -> Tm {Body, Exp, n}          -> Tm {Head, s,  n}
>   Coeh  :: Coeh -> Tm {Body, Exp, n} -> Tm {Body, Exp, n}
>                 -> Tm {Body, Exp, n} -> Tm {Body, Exp, n}  -> Tm {Head, s,  n}
>
>   (:/)  :: {: p :: Part :} => Env {n} {m} -> Tm {p, s, m}  -> Tm {p', Exp, n}

> data Coeh = Coe | Coh deriving (Eq, Show)

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
>   QA :: t -> t -> t -> Elim t   -- applies an equation between functions to equal arguments
>   Sym :: Elim t                 -- symmetry of equality
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
>   Chkd   :: Can                            -- content of a proof for equality checking
>   -- [/Feature = Prop]
>   -- [Feature = Eq]
>   Eq     :: Can                            -- equality type
>   Ext    :: Can                            -- proof by appeal to extensionality
>   -- [/Feature = Eq]
>   -- [Feature = UId]
>   UId    :: Can
>   Tag    :: String -> Can
>   -- [/Feature = UId]
>   -- [Feature = Enum]
>   EnumU  :: Can  -- levitate me!
>   NilE   :: Can  -- levitate me!
>   ConsE  :: Can  -- levitate me! 
>   EnumT  :: Can
>   Ze     :: Can
>   Su     :: Can 
>   -- [/Feature = Enum]

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
>   -- [Feature = Eq]
> pattern EQ _S s _T t  = Eq :- [_S, s, _T, t]
> pattern EXT _P        = Ext :- [_P]
>   -- [/Feature = Eq]
>   -- [Feature = UId]
> pattern UID        = UId :- []
> pattern TAG t      = Tag t :- []
>   -- [/Feature = UId]
>   -- [Feature = Enum]
> pattern ENUMU      = EnumU :- [] 
> pattern NILE       = NilE :- []
> pattern CONSE t e  = ConsE :- [t, e]
> pattern ENUMT e    = EnumT :- [e]
> pattern ZE         = Ze :- []
> pattern SU n       = Su :- [n]
>   -- [/Feature = Enum]

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

> def :: DEF -> EXP
> def d = D d S0 (defOp d)

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

> branchesDEF :: DEF
> branchesDEF = mkDEF
>   [("PRIM",0),("branches",0)]
>   (("E",ENUMU) ->> \_E ->
>    ("P",ARR (ENUMT _E) SET) ->> \_P ->
>    SET)
>   branchesOP
>     where 
>      branchesOP = cases  
>       [  (NilE , eat "P" $ \_P -> emit ONE)
>       ,  (ConsE , eat "T" $ \_T -> eat "E" $ \_E -> eat "P" $ \_P -> emit $
>                     TIMES (_P $$. ZE) 
>                       (wr (D branchesDEF S0 (branchesOP 0)) 
>                           _E (la "n" $ \n -> wr _P (SU n))) )]

> switchDEF :: DEF
> switchDEF = mkDEF
>   [("PRIM",0),("switch",0)]
>   (("E",ENUMU) ->> \_E ->
>    ("x",ENUMT _E) ->> \x ->
>    ("P",ARR (ENUMT _E) SET) ->> \_P ->
>    ("b",wr (D branchesDEF S0 (defOp branchesDEF)) _E _P) ->> \b -> 
>    _P x)
>   switchOP
>     where
>      switchOP = cases  
>        [  (NilE , cases [])
>        ,  (ConsE , eat "T" $ \_T -> eat "E" $ \_E -> cases 
>             [  (Ze , eat "P" $ \_P -> eat "b" $ \b -> emit (b $$ Hd))
>             ,  (Su , eat "x" $ \x -> eat "P" $ \_P -> eat "b" $ \b ->
>                        emit (wr (D switchDEF S0 (switchOP 0)) 
>                                   _E x _P (b $$ Tl)))  ]) ]

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


> exp :: Tm {p, s, n} -> Tm {p, Exp, n}
> exp = unsafeCoerce
> {-
> exp (L a b c) = L a b c
> exp (LK a) = LK a
> exp (a :- b) = a :- b
> exp (a :$ b) = exp a :$ b
> exp (V i) = V i
> exp (P l) = P l
> exp (Refl _S s) = Refl _S s
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
> eval {s} g (Refl _X x) = Refl (g :/ _X) (g :/ x) :$ B0
> eval {Val} g (Coeh Coe _S _T _Q s) = fst (coeh (g // _S) (g // _T) (g // _Q) (g // s))
> eval {Val} g (Coeh Coh _S _T _Q s) = snd (coeh (g // _S) (g // _T) (g // _Q) (g // s))
> eval {Exp} g c@(Coeh _ _ _ _ _) = g :/ c
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
> apply {s} (CON t) Out = eval {s} ENil t
> -- [Feature = Eq]
> apply {s} (Ext :- [f]) (QA a b q) =
>   apply {s} (apply {s} (apply {s} (eval {s} ENil f) (A a)) (A b)) (A q)
> apply {_} (Refl _F f :$ B0) (QA s _ q) | isRefl (ENil // q :: VAL) = case ev _F of
>   PI _S _T -> Refl (_T $$. s) (f $$. s) :$ B0
> apply {_} q Sym | isRefl (ENil // q :: VAL) = q
> apply {_} (r@(Refl _T t) :$ B0) Hd = case (ev _T, ev t) of
>   (SET, PI _S _T) -> Refl SET _S :$ B0
>   (SET, SIGMA _S _T) -> Refl SET _S :$ B0
>   (SIGMA _S _T, p) -> Refl _S (exp (p $$ Hd)) :$ B0
>   (PROP, p) -> la "p" $ \ p -> p
>   _ -> r :$ (B0 :< Hd)
> apply {_} (r@(Refl _T t) :$ B0) Tl = case (ev _T, ev t) of
>   (SET, PI _S _T) -> Refl (_S --> SET) _T :$ B0
>   (SET, SIGMA _S _T) -> Refl (_S --> SET) _T :$ B0
>   (SIGMA _S _T, p) -> Refl (_T $$. (p $$ Hd)) (exp (p $$ Tl)) :$ B0
>   (PROP, p) -> la "p" $ \ p -> p
>   _ -> r :$ (B0 :< Tl)
> apply {_} (h :$ (ss :< Sym)) Sym = h :$ ss
> apply {s} (PAIR a b) Sym = PAIR (apply {Exp} a Sym) (apply {Exp} b Sym)
> apply {s} (CON z) Sym = CON z
> apply {s} (Ext :- [f]) Sym = Ext :- [la "a" $ \ a -> la "b" $ \ b -> la "q" $ \ q ->
>   nix f :$ (B0 :< A b :< A a :< A (V Fz {- q, yuk -} :$ (B0 :< Sym)) :< Sym)]
> -- [/Feature = Eq]
> apply {s} (h :$ ss) a = h :$ (ss :< fmap exp a)
> apply {Exp} (g :/ t) a = (g :/ t) :$ (B0 :< fmap exp a)
> apply {s} x a = error $ show x ++ " $$ " ++ show a

This thing does coercion and coherence.

> coeh :: VAL -> VAL -> VAL -> VAL -> (VAL, VAL)
> coeh _S _ _Q s | isRefl _Q = (s, Refl (exp _S) (exp s) :$ B0)
> coeh SET SET _ _S = (_S, Refl SET (exp _S) :$ B0)
> coeh (PI _S _T) (PI _S' _T') _Q f =
>  (let _QS = _Q $$ Hd $$ Sym
>   in  la "s'" $ \ s' ->
>       let  s = Coeh Coe (nix _S') (nix _S) (nix _QS) s' :$ B0
>            q = Coeh Coh (nix _S') (nix _S) (nix _QS) s' :$ (B0 :< Sym)
>       in  Coeh Coe (nix _T :$ (B0 :< A s)) (nix _T' :$ (B0 :< A s'))
>              (nix _Q :$ (B0 :< Tl :< QA s s' q)) (nix f :$ (B0 :< A s)) :$ B0
>  , Coeh Coh (PI _S _T) (PI _S' _T')  (exp _Q) (exp f) :$ B0)
> coeh (SIGMA _S _T) (SIGMA _S' _T') _Q p =
>   let s = p $$ Hd
>       (s', q) = coeh (ev _S) (ev _S') (_Q $$ Hd) s'
>       (t', q') = coeh (ev _T $$. s) (ev _T' $$. s') (_Q $$ Tl $$ QA s s' q) (p $$ Tl)
>   in  (PAIR (exp s') (exp t'), PAIR (exp q) (exp q'))
> coeh (PRF _) (PRF _) _Q p = (_Q $$ Hd $$. p, ZERO)

> coeh _S _T _Q s = (Coeh Coe (exp _S) (exp _T) (exp _Q) (exp s) :$ B0,
>                    Coeh Coh (exp _S) (exp _T) (exp _Q) (exp s) :$ B0)

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

> nix :: {: p :: Part :} => Tm {p, s, Z}  -> Tm {p', Exp, n}
> nix e = ENix :/ e

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

We have a sound but incomplete test for whether an equality proof is
by reflexivity, the basis for proof compaction and various other
optimizations.

> isRefl :: VAL -> Bool
> isRefl (Refl _ _ :$ es) = isReflSp es 
> isRefl (_ :- es) = all (isRefl . ev) es
> isRefl _ = False

> isReflSp :: Bwd (Elim EXP) -> Bool
> isReflSp B0 = True
> isReflSp (es :< QA _ _ q) = isReflSp es && isRefl (ev q)
> isReflSp (es :< _) = isReflSp es

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

> forlambdabletran :: String -> VAL -> Maybe (ParamKind, String, TY, Tm {Body, s, Z} -> TY)
> forlambdabletran c (PI s t)         = 
>   Just (ParamLam, fortran c [ev t] undefined, s, (t $$.))
> forlambdabletran c (PRF _P) = case ev _P of
>   (PI s p)  -> 
>     Just (ParamAll, fortran c [ev p] undefined, s, \v -> PRF (p $$ A v))
>   _         -> (|)
> forlambdabletran _ _                = Nothing

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
> ugly xs (Refl _S s) = "(refl " ++ ugly xs _S ++ " " ++ ugly xs s ++ ")"
> ugly xs (Coeh Coe _S _T _Q s) =
>   "(coe " ++ ugly xs _S ++ " " ++ ugly xs _T ++ " " ++ ugly xs _Q ++ " " ++ ugly xs s ++ ")"
> ugly xs (Coeh Coh _S _T _Q s) =
>   "(coe " ++ ugly xs _S ++ " " ++ ugly xs _T ++ " " ++ ugly xs _Q ++ " " ++ ugly xs s ++ ")"
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

> partCapture :: pi (m :: Nat). [ EXP ] -> EXP -> Tm {Body, Exp, m}
> partCapture {m} e t = (Just $ (map wk e) ++ (Data.Foldable.foldr (\i l -> (V i :$ B0) : l) [] (vDownFromF {m})) , INix) :/ t

> partCapture' :: {: m :: Nat :} => [ EXP ] -> EXP -> Tm {Body, Exp, m}
> partCapture' = partCapture {: m :: Nat :} 

> piLift :: pi (n :: Nat). BVec {n} (String, TY) -> TY -> TY
> piLift {n} bs t = pil {n} bs (capture {n} t) 
>   where
>     pil :: pi (m :: Nat) . BVec {m} (String, TY) -> Tm {Body, Exp, m} -> EXP
>     pil {Z} BV0 t = t
>     pil {S m} (sts :<<<: (s,ty)) t = pil {m} sts $ PI (capture {m} ty) (L ENil s t)

> piLift' :: {: n :: Nat :} => BVec {n} (String, TY) -> TY -> TY
> piLift' = piLift {: n :: Nat :}

> partPiLift :: pi (n :: Nat). [ EXP ] -> BVec {n} (String, TY) -> TY -> TY
> partPiLift {n} e bs t = pil {n} bs (partCapture {n} e t) 
>   where
>     pil ::  pi (m :: Nat) . BVec {m} (String, TY) -> Tm {Body, Exp, m} -> EXP
>     pil {Z} BV0 t = t
>     pil {S m} (sts :<<<: (s, ty)) t = pil {m} sts $ PI (partCapture {m} e ty) (L ENil s t)

> partPiLift' :: {: n :: Nat :} => [ EXP ] -> BVec {n} (String, TY) -> TY -> TY
> partPiLift' = partPiLift {: n :: Nat :}

