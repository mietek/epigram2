
\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable,
>     FunctionalDependencies, UndecidableInstances, PatternGuards #-}

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
> import Data.Maybe
> import Data.Function

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Unsafe.Coerce
> import Debug.Trace

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
>   D     :: DEF      {- Inv: Applied def is not Emit -}     -> Tm {Head, s, n}
>   V     :: Fin {n}      {- dB i -}                         -> Tm {Head, s, n}
>   P     :: (Int, String, TY)    {- dB l -}                 -> Tm {Head, s, n}
>   B     :: DATATY                                          -> Tm {Head, s, n}
>   Refl     :: Tm {Body, Exp, n} -> Tm {Body, Exp, n}       -> Tm {Head, s, n}
>   SetRefl  :: Tm {Body, Exp, n}                            -> Tm {Head, s, n}
>   Coeh  :: Coeh -> Tm {Body, Exp, n} -> Tm {Body, Exp, n}
>                 -> Tm {Body, Exp, n} -> Tm {Body, Exp, n}  -> Tm {Head, s, n}
>
>   (:/)  :: Env {n} {m} -> Tm {Body, Exp, m} -> Tm {p', Exp, n}

> data DATATY =
>   SIMPLDTY Name EXP  -- I :<: SET 
>                 EXP  -- uDs :<: I --> Constrs I 
                
> data Coeh = Coe | Coh deriving (Eq, Show)

> data DEF = DEF  {  defName :: Name
>                 ,  defTy :: TY
>                 ,  defOp :: Operator 
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
>   -- [Feature = Equality]
>   QA :: t -> t -> t -> Elim t   -- applies an equation between functions to equal arguments
>   Sym :: Elim t                 -- symmetry of equality
>   -- [/Feature: = Equality]
>   -- [Feature: = Label]
>   Call :: t -> Elim t
>   -- [/Feature: = Label]
>   deriving (Show, Eq, Foldable, Traversable, Functor)

> instance HalfZip Elim where
>   halfZip (A a) (A b) = (| (A (a, b)) |) 
>   halfZip Hd Hd = (| Hd |) 
>   halfZip Tl Tl = (| Tl |) 
>   halfZip Out Out = (| Out |) 
>   halfZip (QA aa ab ac) (QA ba bb bc) = (| (QA (aa, ba) (ab, bb) (ac, bc)) |) 
>   halfZip Sym Sym = (| Sym |)
>   halfZip _ _ = (|) 

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
>   Eq     :: Can                            -- value equality type
>   SetEq  :: Can                            -- set equality type
>   Ext    :: Can                            -- proof by appeal to extensionality
>   -- [/Feature = Eq]
>   -- [Feature = UId]
>   UId    :: Can
>   Tag    :: String -> Can
>   -- [/Feature = UId]
>   -- [Feature = Enum]
>   EnumT  :: Can
>   Ze     :: Can
>   Su     :: Can 
>   -- [/Feature = Enum]
>   -- [Feature = IDesc]
>   IMu      :: Can  
>   -- [/Feature = IDesc]
>   -- [Feature = Label]
>   Label  :: Can
>   Ret    :: Can
>   -- [/Feature = Label]
>   -- [Feature = List]
>   List :: Can
>   Nil :: Can
>   Cons :: Can
>   -- [/Feature = List]
>   -- [Feature = Scheme]
>   Scheme   :: Can
>   SchTy   :: Can
>   SchPi    :: Can
>   SchImPi  :: Can
>   -- [/Feature = Scheme]
>   -- [Feature = Dubbing]
>   Dub      :: Can
>   -- [/Feature = Dubbing]
>   -- [Feature = Problem]
>   Pro     :: Prob -> Can
>   -- [/Feature = Problem]

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
> pattern CHKD p     = Chkd :- [p]
>   -- [/Feature = Prop]
>   -- [Feature = Eq]
> pattern EQ _S s _T t  = Eq :- [_S, s, _T, t]
> pattern SETEQ _S _T   = SetEq :- [_S, _T]
> pattern EXT _P        = Ext :- [_P]
>   -- [/Feature = Eq]
>   -- [Feature = UId]
> pattern UID        = UId :- []
> pattern TAG t      = Tag t :- []
>   -- [/Feature = UId]
>   -- [Feature = Enum]
> pattern NILE       = CON (PAIR ZE ZERO)
> pattern CONSE t e  = CON (PAIR (SU ZE) (PAIR t (PAIR e ZERO)))
> pattern ENUMT e    = EnumT :- [e]
> pattern ZE         = Ze :- []
> pattern SU n       = Su :- [n]
>   -- [/Feature = Enum]
>   -- [Feature = IDesc]
> pattern IVARN     = ZE
> pattern ICONSTN   = SU ZE
> pattern IPIN      = SU (SU ZE)
> pattern IFPIN     = SU (SU (SU ZE))
> pattern ISIGMAN   = SU (SU (SU (SU ZE)))
> pattern IFSIGMAN  = SU (SU (SU (SU (SU ZE))))
> pattern IPRODN    = SU (SU (SU (SU (SU (SU ZE)))))

> pattern IMU _I _D i   = IMu :- [_I, _D, i] 
> pattern IVAR i        = CON (PAIR IVARN     (PAIR i ZERO))
> pattern IPI s t       = CON (PAIR IPIN      (PAIR s (PAIR t ZERO)))
> pattern IFPI s t      = CON (PAIR IFPIN     (PAIR s (PAIR t ZERO)))
> pattern ISIGMA s t    = CON (PAIR ISIGMAN   (PAIR s (PAIR t ZERO)))
> pattern IFSIGMA s t   = CON (PAIR IFSIGMAN  (PAIR s (PAIR t ZERO)))
> pattern ICONST p      = CON (PAIR ICONSTN   (PAIR p ZERO))
> pattern IPROD u x y   = CON (PAIR IPRODN    (PAIR u (PAIR x (PAIR y ZERO))))
>   -- [/Feature = IDesc]
>   -- [Feature = Label]
> pattern LABEL t l  = Label :- [t, l]
> pattern RET x      = Ret :- [x]
>   -- [/Feature = Label]
>   -- [Feature = List]
> pattern LIST _A = List :- [_A] 
> pattern NIL = Nil :- [] 
> pattern CONS a as = Cons :- [a, as]
>   -- [/Feature = List]
>   -- [Feature = Scheme]
> pattern SCHEME = Scheme :- []
> pattern SCHTY _T = SchTy :- [_T]
> pattern SCHPI _S _T = SchPi :- [_S,_T]
> pattern SCHIMPI _S _T = SchImPi :- [_S,_T]
>   -- [/Feature = Scheme]
>   -- [Feature = Dubbing]
> pattern DUB u _S s = Dub :- [u, _S, s]
>   -- [/Feature = Dubbing]

> class Problem t where
>   probName :: t -> String
>   probTel :: t -> VAL -- parameter telescope
>   probVal :: t -> [VAL] -> VAL -- Sigma type of result tuple

> data Prob :: * where
>   Blem :: Problem t => t -> Prob

> instance Eq Prob where
>   Blem p == Blem q = probName p == probName q

> instance Show Prob where
>   show (Blem p) = probName p

> pattern Prob p = Pro (Blem p)

> data Operator :: * where
>   Eat    :: Maybe String -> Operator -> Operator 
>   Emit   :: EXP -> Operator
>   Hole   :: Operator
>   Case   :: [(Can , Operator)] -> Operator
>   Split  :: Operator -> Operator
>   GetTag :: String -> (String -> Operator) -> Operator

> type OpMaker = Int -> Operator 

> eat :: String -> ((forall t. Wrapper t {Z} => t) -> OpMaker) -> OpMaker 
> eat y b p = let x :: Tm {Head, Exp, Z} ; x = P (p,y,error $ "eat P escapage: " ++ y) 
>             in  Eat (Just y) (b (wrapper x B0) (p + 1))

> speat :: String -> ((forall t. Wrapper t {Z} => t) -> OpMaker) -> OpMaker 
> speat y b p = let x :: Tm {Head, Exp, Z} ; x = P (p,y,error "speat") 
>               in  Split (Eat (Just y) (b (wrapper x B0) (p + 1)))

> emit :: EXP -> OpMaker 
> emit x _ = Emit x

> split :: OpMaker -> OpMaker 
> split o i = Split (o i)

> cases :: [(Can , OpMaker)] -> OpMaker
> cases ps i = Case $ map (\(c,om) -> (c,om i)) ps

> gettag :: String -> (String -> OpMaker) -> OpMaker
> gettag s f i = GetTag s $ \s' -> f s' i

> def :: DEF -> EXP
> def d = D d :$ B0

> mkDEF :: Name -> TY -> OpMaker -> DEF
> mkDEF nom ty f = DEF
>  { defName = nom
>  , defTy   = ty
>  , defOp   = f 0
>  }


> eats :: [String] -> Operator -> Operator
> eats [] o = o
> eats (n : ns) o = Eat (Just n) (eats ns o) 

> instance Show Operator where
>   show (Eat (Just s) o) = "(Eat " ++ s ++ show o ++ ")"
>   show (Eat Nothing o)  = "(Eat Nothing " ++ show o ++ ")"
>   show (Emit t)         = "(Emit " ++ show t ++ ")"
>   show Hole             = "Hole"
>   show _                = "oooo"

> type Env n m = (LEnv {n}, IEnv {n, m})

> type LEnv n = [(Int, Tm {Body, Exp, n})]

> data IEnv :: {Nat, Nat} -> * where
>  INix   :: IEnv {n, Z}
>  INil   :: IEnv {n, n}
>  (:<<:)  :: IEnv {m, n} -> Tm {Body, s, Z} -> IEnv {m, S n} 


> (!.!) :: IEnv {Z, n} -> Fin {n} -> Tm {Body, Exp, Z}
> (ez :<<: e) !.! Fz = exp e 
> (ez :<<: e) !.! Fs i = ez !.! i

> (<:<) :: Env {m} {n} -> EXP -> Env {m} {S n}
> (gl, gi) <:< e = (gl, gi :<<: e)

> (<+<) :: Env {Z} {n} -> Env {n} {o} -> Env {Z} {o}
> (gl, gi) <+< (gl', gi') = (gln, gi <<< gi')
>   where 
>    (<<<) :: forall m n o. IEnv {Z, n} -> IEnv {n, o} -> IEnv {Z, o}
>    g <<< INix = INix
>    g <<< INil = g
>    g <<< (g' :<<: e) = (g <<< g') :<<: ((gl, INil) <:/> exp e)
>    gln = unionBy ((==) `on` fst)
>              (map (\(l,x) -> (l , (gl, gi) <:/> exp x)) gl') gl

> pattern ENil = ([], INil)
> pattern ENix = ([], INix)

> (<:/>)  ::  {: p' :: Part :} =>
>             Env {Z} {m} -> Tm {Body, Exp, m}  -> Tm {p', Exp, Z}
> g <:/> t = help {: p' :: Part :} g t where
>   help :: forall n m.
>           pi (p' :: Part).
>           Env {Z} {m} -> Tm {Body, Exp, m} -> Tm {p', Exp, Z}
>   help {Body} ([], INil) t = t
>   help {p} g (g' :/ t) = help p (g <+< g') t
>   help {Body} (_, gi) (V i :$ B0) = gi !.! i
>   help {Body} g@(gl, _) t@(P (l, _, _) :$ B0) = case lookup l gl of
>     Just e -> e
>     Nothing -> g :/ t
>   help {Body} g t = g :/ t
>   help {Head} g t = g :/ t


> exp :: Tm {p, s, n} -> Tm {p, Exp, n}
> exp = unsafeCoerce

< exp (L a b c) = L a b c
< exp (LK a) = LK a
< exp (a :- b) = a :- b
< exp (a :$ b) = exp a :$ b
< exp (V i) = V i
< exp (P l) = P l
< exp (Refl _S s) = Refl _S s
< exp (a :/ b) = a :/ b
< exp (D d) = D d

> ev :: Tm {p, Exp, Z} -> VAL
> ev = (ENil //)
 
> eval :: forall m n p s' . pi (s :: Status) . 
>           Env {Z} {n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> eval {s} g (L g' x b) = L (g <+< g') x b
> eval {s} g (LK e) = LK (g <:/> e)
> eval {s} g (CHKD p) = eval {s} g p
> eval {s} g (c :- es) = c :- (fmap (g <:/>) es)
> eval {s} g (h :$ es) = applys {s} (eval {s} g h) (fmap (fmap (g <:/>)) es)
> eval {s} (es, _) (D d) = D d :$ B0
> eval {s} (es, _) (B d) = B d :$ B0
> eval {s} (es, ez) (V i) = eval {s} ENil (ez !.! i)
> eval {s} (es, _) (P lt@(l, _, _)) = case lookup l es of
>   Just t -> eval {s} ENil t
>   Nothing -> P lt :$ B0
> eval {s} g (Refl _X x) = Refl (g <:/> _X) (g <:/> x) :$ B0
> eval {s} g (SetRefl _X) = SetRefl (g <:/> _X) :$ B0
> eval {Val} g (Coeh c _S _T _Q x) = let _S' = (g // _S) ; _T' = (g // _T) ; _Q' = (g // _Q) ; x' = (g // x)
>                                    in case (c,coeh _S' _T' _Q' x') of
>                                         (Coe, Just (e,h)) -> e
>                                         (Coh, Just (e,h)) -> h
>                                         (_,Nothing) -> Coeh c (exp _S') (exp _T') (exp _Q') (exp x') :$ B0 
> eval {Exp} g c@(Coeh _ _ _ _ _) = g <:/> exp (c :$ B0)
> eval {s} g (g' :/ e) = eval {s} (g <+< g') e

> (//) :: {:s :: Status:} => Env {Z} {n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> (//) = evalEager {:s :: Status:}

> apply :: forall s' . pi (s :: Status) . 
>          Tm {Body, s, Z} -> Elim (Tm {Body, s', Z}) -> Tm {Body, s, Z} 
> apply {s} (L (gl, gi) _ b) (A a) = eval {s} (gl, gi :<<: a) b 
> apply {s} (LK e) _ = eval {s} ENil e

< apply {s} (D d es (Eat _ o)) (A a) = mkD {s} d (es :<!: exp a) o  
< apply {Val} (D d es (Case os)) (A a) = 
<   case (ENil // a :: VAL) of -- check that it's canonical
<     (c :- as) -> case lookup c os of
<       (Just o) -> foldl ($$.) (mkD {Val} d (SCase c (length as) es) o) as
<       Nothing -> error ("You muppet: " ++ show c ++ " " ++ show (defName d))             
<     x -> D d (es :<!: exp x) (StuckCase os) :$ B0
< apply {Val} (D d es (Split o)) (A a) = 
<   mkD {Val} d (SSplit es) o $$. ((ENil :/ a) :$ (B0 :< Hd)) $$. ((ENil :/ a) :$ (B0 :< Tl))
< apply {Exp} d@(D _ _ _) a = (ENil :/ d) :$ (B0 :< fmap exp a)  

> apply {Val} (D d :$ az) a 
>   | Just e <- runOp (defOp d) B0 (trail (az :< fmap exp a)) = e
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
>   (SIGMA _S _T, p) -> Refl _S (exp (p $$ Hd)) :$ B0
>   (PROP, p) -> la "p" $ \ p -> p
>   _ -> r :$ (B0 :< Hd)
> apply {_} (r@(SetRefl _T) :$ B0) Hd = case (ev _T) of
>   (PI _S _T) -> SetRefl _S :$ B0
>   (SIGMA _S _T) -> SetRefl _S :$ B0
>   _ -> r :$ (B0 :< Hd)
> apply {_} (r@(Refl _T t) :$ B0) Tl = case (ev _T, ev t) of
>   (SIGMA _S _T, p) -> Refl (_T $$. (p $$ Hd)) (exp (p $$ Tl)) :$ B0
>   (PROP, p) -> la "p" $ \ p -> p
>   _ -> r :$ (B0 :< Tl)
> apply {_} (r@(SetRefl _T) :$ B0) Tl = case (ev _T) of
>   (PI _S _T) -> la "s" $ \s -> la "t" $ \t -> la "q" $ \q ->  Refl (nix _S --> SET) (nix _T) :$ (B0 :< QA s t q :< Out)
>   (SIGMA _S _T) -> la "s" $ \s -> la "t" $ \t -> la "q" $ \q ->  Refl (nix _S --> SET) (nix _T) :$ (B0 :< QA s t q :< Out)
>   _ -> r :$ (B0 :< Tl)
> apply {_} (Refl SET _T :$ B0) Out = SetRefl _T :$ B0 
> apply {_} (h :$ (ss :< Sym)) Sym = h :$ ss
> apply {s} (PAIR a b) Sym = PAIR (apply {Exp} a Sym) (apply {Exp} b Sym)
> apply {s} (CON z) Sym = CON z
> apply {s} (Ext :- [f]) Sym = Ext :- [la "a" $ \ a -> la "b" $ \ b -> la "q" $ \ q ->
>   nix f :$ (B0 :< A b :< A a :< A (V Fz {- q, yuk -} :$ (B0 :< Sym)) :< Sym)]
> -- [/Feature = Eq]
> -- [Feature = Label]
> apply {s} (RET t) (Call l) = eval {s} ENil t
> -- [/Feature = Label]
> apply {s} (h :$ ss) a = h :$ (ss :< fmap exp a)
> apply {Exp} (g :/ t) a = (g <:/> t) :$ (B0 :< fmap exp a)
> apply {s} x a = error $ show x ++ " $$ " ++ show a

> ($$) :: {:s :: Status:} => 
>         Tm {Body, s, Z} -> Elim (Tm {Body, s', Z}) -> Tm {Body, s, Z}
> ($$) = applyEager {:s :: Status:}

> ($$.) :: {:s :: Status:} => 
>         Tm {Body, s, Z} -> Tm {Body, s', Z} -> Tm {Body, s, Z}
> f $$. a = f $$ A a 

> applys :: pi (s :: Status) . 
>           Tm {Body, s, Z} -> Bwd (Elim EXP) -> Tm {Body, s, Z}
> applys {Val} (D d :$ az) az' = 
>   case runOp (defOp d) B0 (trail az ++ trail az') of
>     Just e -> e
>     Nothing -> D d :$ (az <+> az') 
> applys {s} v B0 = v
> applys {s} v (ez :< e) = apply {s} (applys {s} v ez) e

> ($$$) :: {:s :: Status:} => 
>          Tm {Body, s, Z} -> Bwd (Elim EXP) -> Tm {Body, s, Z}
> ($$$) = applys {:s :: Status:}

> ($$$.) :: {:s :: Status:} => 
>          Tm {Body, s, Z} -> Bwd EXP -> Tm {Body, s, Z}
> f $$$. as = f $$$ fmap A as

> nix :: Tm {Body, s, Z}  -> Tm {p', Exp, n}
> nix e = ENix :/ exp e

|runOp| applies a spine to an operator, in an attempt to find an |Emit|:

> runOp :: Operator -> Bwd EXP -> [ Elim EXP ] -> Maybe (Tm {Body, Val, Z})
> runOp (Emit t) oaz as = Just $ 
>   applys {Val} (eval {Val} (zip [0..] (trail oaz),INix) t) (bwdList as)
> runOp (Eat _ o) oaz (A a : as) =  runOp o (oaz :< a) as
> runOp (Case os) oaz (A a : as) | c :- cas <- (ENil // a :: VAL) =
>   case lookup c os of
>     Just o -> runOp o oaz (map A cas ++ as)
>     Nothing -> error ("OpCase found Can it didn't like: " ++ show c)
> runOp (Split o) oaz (A a : as) =
>   runOp o oaz (A ((ENil <:/> a) :$ (B0 :< Hd)) : 
>                A ((ENil <:/> a) :$ (B0 :< Tl)) : as)
> runOp (GetTag s f) oaz (A a : as) | TAG s <- ev a = runOp (f s) oaz as
> runOp (GetTag s f) oaz (A a : as) = runOp (f s) oaz as
> runOp _ _ _ = Nothing 

This thing does coercion and coherence.

> coeh :: VAL -> VAL -> VAL -> VAL -> Maybe (VAL, VAL)
> coeh _S _ _Q s | isRefl _Q = Just (s, Refl (exp _S) (exp s) :$ B0)
> coeh SET SET _ _S = Just (_S, Refl SET (exp _S) :$ B0)
> coeh (PI _S _T) (PI _S' _T') _Q f = Just
>  (let _QS = _Q $$ Hd $$ Sym
>   in  la "s'" $ \ s' ->
>       let  s = Coeh Coe (nix _S') (nix _S) (nix _QS) s' :$ B0
>            q = Coeh Coh (nix _S') (nix _S) (nix _QS) s' :$ (B0 :< Sym)
>       in  Coeh Coe (nix _T :$ (B0 :< A s)) (nix _T' :$ (B0 :< A s'))
>              (nix _Q :$ (B0 :< Tl :< A s :< A s' :< A q)) (nix f :$ (B0 :< A s)) :$ B0
>  , Coeh Coh (PI _S _T) (PI _S' _T')  (exp _Q) (exp f) :$ B0)
> coeh (SIGMA _S _T) (SIGMA _S' _T') _Q p =
>   let s = p $$ Hd
>       (s', q) = (Coeh Coe _S _S' (exp (_Q $$ Hd)) (exp s') :$ B0 , Coeh Coh _S _S' (exp (_Q $$ Hd)) (exp s') :$ B0)
>       (t', q') = (Coeh Coe (_T $$. s) (_T' $$. s') (exp (_Q $$ Tl $$ A s $$ A s' $$ A q)) (exp (p $$ Tl)) :$ B0
>                  ,Coeh Coh (_T $$. s) (_T' $$. s') (exp (_Q $$ Tl $$ A s $$ A s' $$ A q)) (exp (p $$ Tl)) :$ B0)
>   in  Just (PAIR (exp s') (exp t'), PAIR (exp q) (exp q'))
> coeh (PRF _) (PRF _) _Q p = Just (_Q $$ Hd $$. p, ZERO)

> coeh _S _T _Q s = Nothing

<                   (Coeh Coe (exp _S) (exp _T) (exp _Q) (exp s) :$ B0,
<                    Coeh Coh (exp _S) (exp _T) (exp _Q) (exp s) :$ B0)


> fortran :: String -> [Tm {Body, Val, n}] -> Tm {Body, Val, n} -> String
> fortran _ (L _ s _:_) _ = s
> fortran _ (D d :$ as : []) _ | Just s <- stillEating (defOp d) as = s
>   where stillEating (Eat s _) B0 = s
>         stillEating (Eat _ d) (as :< _) = stillEating d as
>         stillEating _ _ = Nothing
> fortran s (_:x) y = fortran s x y
> fortran s [] _ = s

> wk :: Tm {Body, s, Z} -> Tm {p, Exp, n}
> wk t = ([], INix) :/ exp t

> (***) = TIMES
> (-->) = ARR
> (==>) = ARR . PRF
> infixr 5 ==>, -->, ***

We have a sound but incomplete test for whether an equality proof is
by reflexivity, the basis for proof compaction and various other
optimizations.

> isRefl :: VAL -> Bool
> isRefl (SetRefl _ :$ es) = isReflSp es 
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
> ugly xs (P (i, s, t)) = "(" ++ s ++ " = " ++ show i ++ ")"
> ugly xs (Refl _S s) = "(refl " ++ ugly xs _S ++ " " ++ ugly xs s ++ ")"
> ugly xs (SetRefl _S) = "(srefl " ++ ugly xs _S ++ ")"
> ugly xs (Coeh Coe _S _T _Q s) =
>   "(coe " ++ ugly xs _S ++ " " ++ ugly xs _T ++ " " ++ ugly xs _Q ++ " " ++ ugly xs s ++ ")"
> ugly xs (Coeh Coh _S _T _Q s) =
>   "(coe " ++ ugly xs _S ++ " " ++ ugly xs _T ++ " " ++ ugly xs _Q ++ " " ++ ugly xs s ++ ")"
> ugly xs (D d) = show (defName d)
> ugly xs (B (SIMPLDTY na _ _)) = "B" ++ show na  
> ugly xs (g :/ e) = uglyEnv xs g e
> ugly _ _ = "???"

> uglyEnv :: Vec {n} String -> Env {n} {m} -> Tm {p, s, m} -> String
> uglyEnv xs ([], INil)  e = "(ENil :/ " ++ ugly xs e ++ ")"
> uglyEnv xs ([], INix)  e = "(ENix :/ " ++ ugly V0 e ++ ")"
> uglyEnv xs (as, INix)  e = "((" ++ uglyLEnv xs as ++ ", INix) :/ " ++ ugly V0 e ++ ")"
> uglyEnv xs (as, INil)  e = "((" ++ uglyLEnv xs as ++ ", INil) :/ " ++ ugly xs e ++ ")"
> uglyEnv xs ([], ie)     e = "(([], " ++ s  ++ ") :/ " ++ ugly ys e ++ ")"
>   where (s, ys) = uglyIEnv xs ie
> uglyEnv xs (as, ie)     e = "((" ++ uglyLEnv xs as ++", " ++ s ++ ") :/ " ++ ugly ys e ++ ")"
>   where (s, ys) = uglyIEnv xs ie

> uglyIEnv :: Vec {n} String -> IEnv {n, m} -> (String, Vec {m} String)
> uglyIEnv xs INil        = ("INil", xs)
> uglyIEnv xs INix        = ("INix", V0)
> uglyIEnv xs (g :<<: t)  = (s ++ " :<<: " ++ ugly V0 t, ("V" ++ show (vlength ys) :>>: ys))
>   where (s, ys) = uglyIEnv xs g

> uglyLEnv :: Vec {n} String -> [(Int,Tm {Body, Exp, n})] -> String
> uglyLEnv xs as = "[" ++ 
>   intercalate "," (map (\ (l,t) -> "(" ++ show l ++ ", " ++ ugly xs t ++ ")") as) ++ "]"

> uglyElim :: Vec {n} String -> Elim (Tm {p, s, n}) -> String
> uglyElim v (A e) = ugly v e
> uglyElim v Hd = "!"
> uglyElim v Tl = "-"
> uglyElim v Out = "%"
> uglyElim v (Call e) = "<<Call " ++ ugly v e ++ ">>"

> instance {:n :: Nat:} => Show (Tm {p, s, n}) where
>   show t = ugly (fmap (\ i -> "v" ++ show i) vUpTo') t


> piLift' :: {: n :: Nat :} => BVec {n} (Int, String, TY) -> TY -> TY
> piLift' = piLift {: n :: Nat :}

> piLift :: pi (n :: Nat). BVec {n} (Int, String, TY) -> TY -> TY
> piLift {n} bs t = spil {n} bs (capture {n} (fmap (\ (l, _, _) -> l) bs) t)
>   where
>     spil :: pi (m :: Nat) . BVec {m} (Int, String, TY) -> Tm {Body, Exp, m} -> EXP
>     spil {Z} BV0 t = t
>     spil {S m} (sts :<<<: (_, s, ty)) t = 
>       spil {m} sts $ PI (capture {m} (fmap (\ (l, _, _) -> l) sts) ty) (L ENil s t)


> lamLift' :: {: n :: Nat :} => BVec {n} (Int, String, TY) -> EXP -> EXP
> lamLift' = lamLift {: n :: Nat :}

> lamLift :: pi (n :: Nat) . BVec {n} (Int, String, TY) -> EXP -> EXP
> lamLift {n} bs = lamWrap {n} bs . capture n (fmap (\ (l, _, _) -> l) bs)
>   where
>     lamWrap :: pi (n :: Nat) . BVec {n} (Int, String, TY) -> Tm {Body, Exp, n} -> EXP
>     lamWrap {Z}   BV0 t = t
>     lamWrap {S n} (sts :<<<: (_, s, _)) t = lamWrap {n} sts (L ENil s t)



> capture' :: {: n :: Nat :} => BVec {n} Int ->
>                  EXP -> Tm {Body, Exp, n}
> capture' = capture {: n :: Nat :}

> capture :: forall a b. pi (n :: Nat). BVec {n} Int ->
>                 EXP -> Tm {Body, Exp, n}
> capture {n} bs t = (splif {n} bs (bvDownFromF {n}) [], INix) :/ t
>   where
>     splif :: forall a b m . pi (n :: Nat). BVec {n} Int -> 
>              BVec {n} (Fin {m}) -> [ (Int, Tm {Body, Exp, m}) ] -> 
>              [ (Int, Tm {Body, Exp, m}) ]
>     splif {Z} _ _ es = es
>     splif {S n} (ls :<<<: l) (vs :<<<: v) es = 
>       splif {n} ls vs ((l,V v :$ B0) : es)




> isCan :: Tm {Body, Val, n} -> Maybe (Can, [Tm {Body, Exp, n}])
> isCan (c :- es)  = Just (c, es)
> isCan _          = Nothing






> evalEager :: forall m n p s' . pi (s :: Status) .
>           Env {Z} {n} -> Tm {p, s', n} -> Tm {Body, s, Z}
> evalEager {s} g (L g' x b)  = L (g <+< g') x b
> evalEager {s} g (LK b)      = LK (exp (evalEager {s} g b))
> evalEager {s} g (c :- es)   = c :- (map (exp . evalEager {s} g) es)
> evalEager {s} g (g' :/ e)   = evalEager {s} (g <+< g') e
> evalEager {s} g (h :$ es)   = applysEager {s} (evalEager {s} g h)
>                                                   (fmap (fmap (exp . evalEager {s} g)) es)
> evalEager {s} (_, gi) (V i)           = evalEager {s} ENix (gi !.! i)
> evalEager {s} (gl, _) (P (l, x, ty))  = case lookup l gl of
>     Just t   -> evalEager {s} ENix t
>     Nothing  -> P (l, x, ty) :$ B0
> evalEager {Val} g (D (DEF _ _ (Emit t)))  = evalEager {Val} ENix t
> evalEager {s} g (D d)                     = D d :$ B0
> evalEager {s} g (B d)                     = B d :$ B0
> evalEager {s} g (Refl _X x) = Refl (exp (evalEager {s} g _X)) (exp (evalEager {s} g x)) :$ B0
> evalEager {s} g (SetRefl _X) = SetRefl (exp (evalEager {s} g _X))  :$ B0
> evalEager {s} g (Coeh c _S _T _Q x) = let _S' = (evalEager {Val} g _S) 
>                                           _T' = (evalEager {Val} g _T) 
>                                           _Q' = (evalEager {Val} g _Q) 
>                                           x' = (evalEager {Val} g x)
>                                       in case (c,coeh _S' _T' _Q' x') of
>                                            (Coe, Just (e,h)) -> evalEager {s} ENil e
>                                            (Coh, Just (e,h)) -> evalEager {s} ENil h
>                                            (_,Nothing) -> Coeh c (exp _S') (exp _T') (exp _Q') (exp x') :$ B0 
> evalEager {s} g e = error $ "evalEager: missing: " 

> applysEager ::  pi (s :: Status) . 
>                     Tm {Body, s, Z} -> Bwd (Elim EXP) -> Tm {Body, s, Z}
> applysEager {s} h B0         = h
> applysEager {s} h (es :< e)  = applyEager {s} (applysEager {s} h es) e 


> applyEager ::  forall s' . pi (s :: Status) . 
>                    Tm {Body, s, Z} -> Elim (Tm {Body, s', Z}) -> Tm {Body, s, Z} 
> applyEager {s}    (L g x b)    (A t)  = evalEager {s} (g <:< exp t) b 
> applyEager {s}    (LK b)       (A _)  = evalEager {s} ENix b
> applyEager {s}    (PAIR h _)   Hd     = evalEager {s} ENix h
> applyEager {s}    (PAIR _ t)   Tl     = evalEager {s} ENix t
> applyEager {Val}  (D d :$ az)  a
>   | Just e <- runOpEager (defOp d) B0 (trail (az :< fmap exp a)) = e
> applyEager {s}    (h :$ az)    a      = h :$ (az :< fmap exp a)
> applyEager {s} (CON t) Out = evalEager {s} ENil t
> -- [Feature = Eq]
> applyEager {s} (Ext :- [f]) (QA a b q) =
>   applyEager {s} (applyEager {s} (applyEager {s} (evalEager {s} ENil f) (A a)) (A b)) (A q)
> applyEager {s} (Refl _F f :$ B0) (QA x _ q) | isRefl (ENil // q :: VAL) = case ev _F of
>   PI _S _T -> Refl (exp (applyEager {s} (evalEager {s} ENil _T) (A (evalEager {s} ENil x)))) (exp (applyEager {s} (evalEager {s} ENil f) (A (evalEager {s} ENil x)))) :$ B0
> applyEager {s} q Sym | isRefl (ENil // q :: VAL) = evalEager {s} ENil q
> applyEager {s} (r@(Refl _T t) :$ B0) Hd = case (ev _T, ev t) of
>   (SIGMA _S _T, p) -> Refl (exp (evalEager {s} ENil _S)) (exp (applyEager {s} (evalEager {s} ENil p) Hd)) :$ B0
>   (PROP, p) -> la "p" $ \ p -> p
>   _ -> r :$ (B0 :< Hd)
> applyEager {s} (r@(SetRefl _T) :$ B0) Hd = case (ev _T) of
>   (PI _S _T) -> SetRefl (exp (evalEager {s} ENil _S)) :$ B0
>   (SIGMA _S _T) -> SetRefl (exp (evalEager {s} ENil _S)) :$ B0
>   _ -> r :$ (B0 :< Hd)
> applyEager {s} (r@(Refl _T t) :$ B0) Tl = case (ev _T, ev t) of
>   (SIGMA _S _T, p) -> Refl (exp (applyEager {s} (evalEager {s} ENil _T) (A (applyEager {s} (evalEager {s} ENil p) Hd)))) (exp (applyEager {s} (evalEager {s} ENil p) Tl)) :$ B0
>   (PROP, p) -> la "p" $ \ p -> p
>   _ -> r :$ (B0 :< Tl)
> applyEager {s} (r@(SetRefl _T) :$ B0) Tl = case (ev _T) of
>   (PI _S _T) -> Refl (exp (evalEager {s} ENil _S) --> SET) (exp (evalEager {s} ENil _T)) :$ B0
>   (SIGMA _S _T) -> Refl (exp (evalEager {s} ENil _S) --> SET) (exp (evalEager {s} ENil _T)) :$ B0
>   _ -> r :$ (B0 :< Tl)
> applyEager {s} (h :$ (ss :< Sym)) Sym = applysEager {s} (h :$ B0) ss
> applyEager {s} (PAIR a b) Sym = PAIR (exp (applyEager {s} (evalEager {s} ENil a) Sym)) (exp (applyEager {s} (evalEager {s} ENil b) Sym))
> applyEager {s} (CON z) Sym = CON (exp (evalEager {s} ENil z))
> applyEager {s} (Refl SET _T :$ B0) Out = SetRefl _T :$ B0
> applyEager {s} (Ext :- [f]) Sym = Ext :- [la "a" $ \ a -> la "b" $ \ b -> la "q" $ \ q ->
>   nix f :$ (B0 :< A b :< A a :< A (V Fz {- q, yuk -} :$ (B0 :< Sym)) :< Sym)]
> -- [/Feature = Eq]
> -- [Feature = Label]
> applyEager {s} (RET t) (Call l) = evalEager {s} ENil t
> -- [/Feature = Label]
> applyEager {s}    e            a = error $ "applyEager: missing " ++ show e
>                                                ++ " $$ " ++ show a

> runOpEager :: Operator -> Bwd EXP -> [ Elim EXP ] -> Maybe VAL
> runOpEager (Emit t) oaz as = Just $ 
>   applysEager {Val} (evalEager {Val} (zip [0..] (trail oaz),INix) t) (bwdList as)
> runOpEager (Eat _ o) oaz (A a : as) =  runOpEager o (oaz :< a) as
> runOpEager (Case os) oaz (A a : as) | c :- cas <- (ENil // a :: VAL) =
>   case lookup c os of
>     Just o -> runOpEager o oaz (map A cas ++ as)
>     Nothing -> error "OpCase found Can it didn't like"
> runOpEager (Split o) oaz (A a : as) =
>   runOpEager o oaz (A ((ENil <:/> a) :$ (B0 :< Hd)) : 
>                      A ((ENil <:/> a) :$ (B0 :< Tl)) : as)
> runOpEager (GetTag s f) oaz (A a : as) | TAG s <- ev a = runOpEager (f s) oaz as
> runOpEager (GetTag s f) oaz (A a : as) = runOpEager (f s) oaz as
> runOpEager _ _ _ = Nothing 

> evv = evalEager {Val} ENil

> applyScheme :: VAL -> Elim EXP -> EXP
> applyScheme (SCHPI _ _T) a = _T $$ a
> applyScheme (SCHIMPI _ _T) a = _T $$ a

> applysScheme :: VAL -> [ Elim EXP ] -> EXP
> applysScheme s [] = exp s
> applysScheme s (a : as) = applysScheme (ev $ applyScheme s a) as
