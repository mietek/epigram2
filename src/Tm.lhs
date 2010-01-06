\section{Tm}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

> module Tm where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.Identity
> import Data.Either
> import qualified Data.Monoid as M
> import Data.Foldable hiding (foldl)
> import Data.Traversable

> import MissingLibrary
> import BwdFwd
> import Features
> import Root

%endif

%format :$ = ":\!\!\$"
%format :@ = ":\!\!@"
%format :? = ":\!\in"
%format Set = "\star"
%format Pi = "\Pi"
%format :. = "\bullet"
%format :>: = "\ni"
%format :<: = "\in"
%format :=>: = "\Downarrow"

\subsection{Syntax of Terms and Values}


We distinguish |In|Terms (into which we push types) and |Ex|Terms
(from which we pull types).

> data Dir    = In | Ex

This is the by-now traditional bidirectional
type-checking~\cite{turner:bidirectional_tc} story: there are
\emph{checkable} terms that are checked against given types, and there
are \emph{inferable} terms which type are inferred relatively to a
typing context. We push types in checkable terms, pull types from
inferable terms.

We also distinguish the representations of |TT| terms and |VV| values.
We may consider distinguishing (unelaborated) display terms from those which
have been elaborated and hence can be evaluated, but for the moment we
conflate the two cases.


> data Phase  = TT | VV

And, of course, we're polymorphic in the representation of free
variables, like your mother always told you. This gives the following
signature for a term:

> data Tm :: {Dir, Phase} -> * -> * where

We can push types in to:
\begin{itemize}
\item lambda terms;
\item canonical terms;
\item inferred terms; and
\item holes.
\end{itemize}

>   L     :: Scope p x             -> Tm {In, p}   x -- \(\lambda\)
>   C     :: Can (Tm {In, p} x)    -> Tm {In, p}   x -- canonical
>   N     :: Tm {Ex, p} x          -> Tm {In, p}   x -- |Ex| to |In|
>   Q     :: String                -> Tm {In, TT}  x -- hole

And we can infer types from:
\begin{itemize}
\item variables, by reading the context;
\item fully applied operators, by |opTy| defined below;
\item elimination, by the type of the eliminator; and
\item type ascription on a checkable term, by the ascripted type.
\end{itemize}

>   P     :: x                     -> Tm {Ex, p}   x -- parameter
>   V     :: Int                   -> Tm {Ex, TT}  x -- variable
>   (:@)  :: Op -> [Tm {In, p} x]  -> Tm {Ex, p}   x -- fully applied op
>   (:$)  :: Tm {Ex, p} x -> Elim (Tm {In, p} x) -> Tm {Ex, p} x  -- elim
>   (:?)  :: Tm {In, TT} x -> Tm {In, TT} x -> Tm {Ex, TT} x      -- typing

In the world of values, ie. |Tm {In, VV} p|, the neutral terms are
exactly the |N t| terms. Actually, it requires some caution in the way
we deal with operator and how we turn them into values, so this
statement relies on the hypothesis that the evaluation of operators is
correct. More detail below.

To prove that statement, we first show that any |Tm {In, VV} p| which
is not a |N t| is not a neutral term. This obvious as we are left with
lambda and canonicals, which cannot be stuck. Then, we have to prove
that a |N t| in |Tm {In, VV} p| form is a stuck term. We do so by case
analysis on the term |t| inside the |N|:
\begin{itemize}

\item Typing and variable will not let you get a value, so a neutral
value is not one of those.

\item This is also easy if you have a parameter: it is stuck waiting
for its definition.

\item An eliminator in value form consists in an elimination applied
to a value in |Ex|, which is -- by induction -- a neutral term. Hence,
the eliminator is stuck too.

\item The case for fully applied operator is more problematic: we need
one of the arguments to be a |N t|, and to be used by |Op|. This way,
the operation is indeed a neutral term. We can hardly enforce these
constraints in types, so we have to deal with this approximation.

\end{itemize}

Fully applied operators call for some care with |:@|. If you are to
explicitly write a |:@| term wrapped inside a |N|, you must be sure
that the operator is indeed applied to a stuck term \emph{which is
used} by the operator. Similarly, when evaluating for example, we have
been careful in returning a neutral operator if and only if the
operator was consuming a stuck term. As a corollary, if the operator
can be fully computed, then it \emph{must} be so. More tricky but for
the same reason: when building tactics, we are building terms. So,
again, we should be careful of not building a stuck operator for no
good reason.

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
sub-objects (terms or values, as appropriate). Lambda is not included
here: morally, it belongs; practically, adapting |Can| to support
binding complicates the definition. Note the presence of the @import@
She-ism: this means that canonical constructors can be later plugged
in using a She aspect.

> data Can :: * -> * where
>   Set   :: Can t                                   -- set of sets
>   Pi    :: t -> t -> Can t                         -- functions
>   Con   :: t -> Can t
>   import <- CanConstructors
>   deriving (Show, Eq)

The |Elim| functor explains how eliminators are constructed from their
sub-objects. It's a sort of logarithm. Projective eliminators for types
with \(\eta\)-laws go here.

\question{What is that story with logarithms?}

> data Elim :: * -> * where
>   A     :: t -> Elim t                             -- application
>   Out   :: Elim t                                  -- unpacks Con
>   import <- ElimConstructors
>   deriving (Show, Eq)

Other computation is performed by a fixed repertoire of operators. To
construct an operator, you need a name (for scope resolution and
printing), an arity (so the resolver can manage fully applied usage),
a typing rule, and a computation strategy. 


The |opTy| field explains how to label the operator's arguments with
the types they must have and delivers the type of the whole
application: to do that, one must be able to evaluate arguments. It is
vital to check the sub-terms (left to right) before trusting the type
at the end. This corresponds to the following type:

< opTy :: forall t. (t -> VAL) -> [t] -> Maybe ([TY :>: t] , TY)
< opTy ev args = (...)

Where we are provided an evaluator |ev| and the list of arguments,
which length should be the arity of the operator. If the type of the
arguments is correct, we return them labelled with their type and the
type of the result.

However, in order to use |opTy| directly in the tactics, we had to
generalize it. Following the evolution of |canTy| in @Rules.lhs@, we
have adopted the following scheme:

< opTy    :: MonadPlus m => (TY :>: t -> m (s :=>: VAL)) -> 
<                           [t] -> 
<                           m ([s :=>: VAL] , TY)

First, being |MonadPlus| allows a seamless integration in the Tactics
world. Second, we have extended the evaluation function to perform
type-checking at the same time. We also liberalize the return type to
|s|, to give more freedom in the choice of the checker-evaluator. This
change impacts on |exQuote|, |infer|, and |useOp|. If this definition
is not clear now, it should become clear after the definition of
|canTy|.

> data Op = Op
>   { opName  :: String
>   , opArity :: Int
>   , opTy    :: MonadError [String] m =>  (TY :>: t -> m (s :=>: VAL)) -> 
>                                        [t] -> 
>                                        m ([s :=>: VAL] , TY)
>   , opSimp  :: Alternative m => [VAL] -> Root -> m NEU
>   , opRun   :: [VAL] -> Either NEU VAL
>   }

Meanwhile, the |opRun| argument implements the computational
behavior: given suitable arguments, we should receive a value, or
failing that, the neutral term to blame for the failure of
computation. For example, if |append| were an operator, it would
compute if the first list is nil or cons, but complain about the first
list if it is neutral.


\subsection{Useful Abbreviations}

We have some pattern synonyms for common, er, patterns.

> pattern SET       = C Set                   -- set of sets
> pattern ARR s t   = C (Pi s (L (K t)))      -- simple arrow
> pattern PI s t    = C (Pi s t)   -- dependent functions
> pattern CON t     = C (Con t)
> pattern NV n      = N (V n)
> pattern NP n      = N (P n)
> pattern LAV x t   = L (x :. t)
> pattern PIV x s t = PI s (LAV x t)
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

At the moment we do not make a type distinction between display and
elaborated terms, so using the following synonyms is optional.

> type INDTM  = INTM
> type EXDTM  = EXTM

We have special pairs for types going into and coming out of
stuff. That is, we write |typ :>: thing| to say that
|typ| accepts the term |thing|. Conversely, we write |thing :<: typ|
to say that |thing| is of infered type |typ|. Therefore, we can read
|:>:| as ``accepts'' and |:<:| as ``has inferred type''.

> data y :>: t = y :>: t  deriving (Show,Eq)
> infix 4 :>:
> data t :<: y = t :<: y  deriving (Show,Eq)
> infix 4 :<:

As we are discussing syntactic sugar, let me introduce the ``reduces
to'' symbol:

> data t :=>: v = t :=>: v deriving (Show, Eq)
> infix 4 :=>:

With the associated projections:

> valueOf :: (t :=>: v) -> v
> valueOf (_ :=>: v) = v
>
> termOf :: (t :=>: v) -> t
> termOf (t :=>: _) = t

Intuitively, |t :=>: v| can be read as ``the term |t| reduces to the
value |v|''.

\pierre{This implicit conversion is not yet enforced everywhere in the
code. If you find opportunities to enforce it, go ahead. Typically,
you can recognize such case when there is a |(t, VAL)| where the value
in |VAL| has been obtained by evaluation of a thing in |t|}

\subsection{Syntactic Equality}
\label{sec:syntactic_equality}

We use syntactic equality on \(\eta\)-quoted values to implement the
definitional equality.


In the following, we implement definitional equality on terms. In this
case, it's mainly structural.

> instance Eq x => Eq (Tm {d, TT} x) where

First, a bunch of straightforward structural inductions:

>   L s0          == L s1          = s0 == s1
>   C c0          == C c1          = c0 == c1
>   N n0          == N n1          = n0 == n1
>   P x0          == P x1          = x0 == x1
>   V i0          == V i1          = i0 == i1
>   (t0 :$ e0)    == (t1 :$ e1)    = t0 == t1 && e0 == e1
>   (op0 :@ vs0)  == (op1 :@ vs1)  = op0 == op1 && vs0 == vs1

Then, equality in a set means having equal canonical element:

>   (t0 :? _)     == (t1 :? _)     = t0 == t1

Finally, a place-holder, as all terms should be matched by one of the
previous patterns:

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

In this section, we have defined the syntactic equality on terms. The
general definition of syntactic equality remains to be done. It is
the subject of Section~\ref{sec:rules}: there, we rely on
\emph{quotation} to turn values into terms. Once turned into terms, 
we fall back to the equality defined above.


\subsection{References}
\label{sec:references}

References are the key way we represent free variables, declared,
defined, and deluded. References carry not only names, but types and
values, and are shared.

> data REF = (:=) { refName :: Name, refBody :: (RKind :<: TY)}
>   deriving Show -- is shared where possible
> infix 2 :=
>
> instance Eq REF where
>   (x := _) == (y := _) = x == y  -- could use cheeky pointer equality?

A |REF| can either be:
\begin{description}
\item[|DECL|:] used a binder, a declaration
\item[|DEFN|:] computed, a definition
\item[|HOLE|:] not computed yet, a definition-to-be
\item[|FAKE|:] a hysterectomized definition, used to make labels
\end{description}

> data RKind
>   =  DECL
>   |  DEFN VAL
>   |  HOLE
>   |  FAKE
>   deriving Show

We can already define some handy operators on |REF|s. First, we can
turn a |REF| to a |VAL|ue by using |pval|. If the reference is already
reduced, then we simply pick the computed value. Otherwise, it is
dealt as a neutral parameter.

> pval :: REF -> VAL
> pval (_ := DEFN v :<: _)  = v
> pval r                    = N (P r)

Second, we can extract the type of a reference thanks to the following
code:

> pty :: REF -> VAL
> pty (_ := _ :<: ty) = ty


\subsection{Labels}

Labels are tucked into strange places, in order to record the
high-level presentation of low-level stuff.  A typical label is the
neutral application of a fake reference --- a definition whose
hysterectomy stops it computing.

> data Labelled f t
>   = Maybe t :?=: f t
>   deriving (Show)

Label equality is sound but not complete for equality of what has been
labelled.

> instance (Traversable f, HalfZip f, Eq t) => Eq (Labelled f t) where
>   (Just a  :?=: _)  ==  (Just b  :?=: _) | a == b  = True
>   (_       :?=: s)  ==  (_       :?=: t)           = case halfZip s t of
>     Nothing -> False 
>     Just x -> M.getAll (crush (M.All . uncurry (==)) x) 



\subsection{Variable Manipulation}

This is the Very Nice Mangler. A |Mangle f x y| is a record that describes how to deal with
parameters of type |x|, variables and binders, producing terms with parameters
of type |y| and wrapping the results in some applicative functor |f|. It 
contains three fields:
\begin{description}
\item{|mangP|} describes what to do with parameters. It takes a parameter value
               and a spine (a list of eliminators) that this parameter is applied to
               (handy for christening); it must produce an appropriate term.
\item{|mangV|} describes what to do with variables. It takes a de Brujin index
               and a spine as before, and must produce a term.
\item{|mangB|} describes how to update the |Mangle| in response to a given
               binder name.
\end{description}

> data Mangle f x y = Mang
>   {  mangP :: x -> f [Elim (InTm y)] -> f (ExTm y)
>   ,  mangV :: Int -> f [Elim (InTm y)] -> f (ExTm y)
>   ,  mangB :: String -> Mangle f x y
>   }

The |%| operator mangles a term, produing a term with the appropriate parameter
type in the relevant idiom. This is basically a traversal, but calling the
appropriate fields of |Mangle| for each parameter, variable or binder encountered.

> (%) :: Applicative f => Mangle f x y -> Tm {In, TT} x -> f (Tm {In, TT} y)
> m % L (K t)      = (|L (|K (m % t)|)|)
> m % L (x :. t)   = (|L (|(x :.) (mangB m x % t)|)|)
> m % C c          = (|C ((m %) ^$ c)|)
> m % N n          = (|N (exMang m n (|[]|))|)
> m % Q x          = (|(Q x)|)
>
> exMang ::  Applicative f => Mangle f x y ->
>            Tm {Ex, TT} x -> f [Elim (Tm {In, TT} y)] -> f (Tm {Ex, TT} y)
> exMang m (P x)     es = mangP m x es
> exMang m (V i)     es = mangV m i es
> exMang m (o :@ a)  es = (|(| (o :@) ((m %) ^$ a) |) $:$ es|) 
> exMang m (t :$ e)  es = exMang m t (|((m %) ^$ e) : es|)
> exMang m (t :? y)  es = (|(|(m % t) :? (m % y)|) $:$ es|)


The |%%| operator applies a mangle that uses the identity functor.

> (%%) :: Mangle Identity x y -> Tm {In, TT} x -> Tm {In, TT} y
> m %% t = runIdentity $ m % t


%format $:$ = "\mathbin{\$\!:\!\$}"

A |Spine| is a list of eliminators for terms, typically representing a list of
arguments that can be applied to a term with the |$:$| operator.

> type Spine p x = [Elim (Tm {In, p} x)]
>
> ($:$) :: Tm {Ex, p} x -> Spine p x -> Tm {Ex, p} x
> ($:$) = foldl (:$)


Given a list |xs| of |String| parameter names, the |capture| function produces a mangle
that captures those parameters as de Brujin indexed variables.
\question{Do we ever need to do this?}

> capture :: Bwd String -> Mangle Identity String String
> capture xs = Mang
>   {  mangP = \ x ies  -> (|(either P V (h xs x) $:$) ies|)
>   ,  mangV = \ i ies  -> (|(V i $:$) ies|)
>   ,  mangB = \ x -> capture (xs :< x)
>   } where
>   h B0         x  = Left x
>   h (ys :< y)  x
>     | x == y      = Right 0
>     | otherwise   = (|succ (h ys y)|)


The |under i y| mangle binds the variable with de Brujin index |i| to the parameter |y|
and leaves the term otherwise unchanged.

> under :: Int -> x -> Mangle Identity x x
> under i y = Mang
>   {  mangP = \ x ies -> (|(P x $:$) ies|)
>   ,  mangV = \ j ies -> (|((if i == j then P y else V j) $:$) ies|)
>   ,  mangB = \ _ -> under (i + 1) y
>   }


The |underScope| function goes under a binding, instantiating the bound variable
to the given reference.

> underScope :: Scope {TT} x -> x -> InTm x
> underScope (K t)     _ = t
> underScope (_ :. t)  x = under 0 x %% t



%if False


\subsection{Term Construction}

I think that this stuff should disappear with Tactics spreading.

> ($#) :: Int -> [Int] -> InTm x
> f $# xs = N (foldl (\ g x -> g :$ A (NV x)) (V f) xs)

> ($##) :: EXTM -> [INTM] -> INTM
> f $## xs = N (foldl (\g x -> g :$ A x) f xs)

> fortran :: Tm {In, p} x -> String
> fortran (L (x :. _)) | not (null x) = x
> fortran _ = "x"


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
>   traverse _ Out    = (|Out|)
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
>   show (Q "")      = "?"
>   show (Q x)       = "(? " ++ x ++ ")"
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

> instance Traversable f => Functor (Labelled f) where
>   fmap = fmapDefault
> instance (Traversable f, Foldable f) => Foldable (Labelled f) where
>   foldMap = foldMapDefault
> instance Traversable f => Traversable (Labelled f) where
>   traverse f (mt :?=: ft)  = (| traverse f mt :?=: traverse f ft |)

> instance (Traversable f, HalfZip f) => HalfZip (Labelled f) where
>   halfZip (Just a  :?=: fs)  (Just b :?=: ft)  = 
>     (| (Just (a, b)  :?=:) (halfZip fs ft) |)
>   halfZip (_       :?=: fs)  (_      :?=: ft)  = 
>     (| (Nothing  :?=:) (halfZip fs ft) |)

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


%endif
