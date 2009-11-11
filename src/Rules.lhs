\section{Rules}
\label{sec:rules}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, PatternGuards #-}

> module Rules where

> import Control.Applicative
> import Control.Monad

> import Data.Foldable
> import Data.Traversable
> import Data.Maybe

> import BwdFwd
> import Tm
> import Root
> import Rooty
> import Features
> import MissingLibrary

> import {-# SOURCE #-} Tactics

%endif

\subsection{Type-checking Canonicals and Eliminators}

Historically, canonical terms were type-checked by the following
function:

< canTy :: (t -> VAL) -> (Can VAL :>: Can t) -> Maybe (Can (TY :>: t))
< canTy ev (Set,Set)    = Just Set
< canTy ev (Pi s t,Set) = Just (Pi (SET :>: s) ((ARR (ev s) SET) :>: t)
< canTy _  _            = Nothing

If we temporally forget Features, we have here a type-checker that
takes an evaluation function |ev|, a type, and a term to be checked
against this type. When successful, the result of typing is a
canonical term that contains both the initial term and its normalized
form, as we get it during type-checking.

However, in order to implement tactics, we have to generalize this
function. The generalization consists in parameterizing |canTy| with a
type-directed function |(TY :>: t) -> s|, which is equivalent to 
|TY -> t -> s|. Because we are still using the concept of evaluation, both
functions are fused into a single one, of type: 
|TY -> t -> (s,VAL)|. To support the use of tactics, which can fail to produce a
value, we extend this type to |TY -> t -> Maybe (s,VAL)|

Hence, by defining an appropriate function |tc|, we can recover the
previous definition of |canTy|. We can also do much more: intuitively,
we can write any type-directed function in term of |canTy|. That is,
any function traversing the types derivation tree can be expressed
using |canTy|. 

< canTy :: (TY -> t -> Maybe (s :=>: VAL)) -> (Can VAL :>: Can t) -> Maybe (Can s)
< canTy tc (Set :>: Set)     =  Just Set
< canTy tc (Set :>: Pi s t)  = do
<   (s,sv) <-  SET `tc` s 
<   (t,_) <- ARR sv SET  `tc` t
<   return $ Pi s t
< import <- CanTyRules
< canTy  _  _                 = Nothing

If you think about it, what we have defined about could be generalized
once again. Indeed, if we jump inside a |MonadPlus|, we are still able
to write the code above. However, doing that, we regain the mental
sanity we lost with the typechecking-evaluating function: we consider
a |t -> m VAL| which stands for an evaluator in the monad. Some
type-checking might happen under the hood but we don't have to be
aware of that. In the end, we get a function quite similar to the
original one.

\pierre{When the epig people get use to this new |canTy|, we can
        scratch the previous code.}

> canTy :: MonadPlus m => (t -> m VAL) -> (Can VAL :>: Can t) -> m (Can (TY :>: t))
> canTy ev (Set :>: Set)     = return Set
> canTy ev (Set :>: Pi s t)  = do
>   sv <-  ev s
>   tv <- ev t
>   return $ Pi (SET :>: s) (ARR sv SET :>: t)
> import <- CanTyRules
> canTy  _  _                 = mzero


Type-checking elimination forms is more standard and mirrors the
initial definition of |canTy|. |elimTy| is provided with an evaluator
of |t -> VAL|, a value |f| of inferred typed |t|, ie. |f :<: t| of
|VAL :<: Can VAL|, an eliminator of |Elim t|. If the operation is
type-correct, it computes the type of the argument, ie. the
eliminator, of |Elim (TY :>: t)| and the type of the result |TY|.

> elimTy :: (t -> VAL) -> (VAL :<: Can VAL) -> Elim t ->
>           Maybe (Elim (TY :>: t),TY)
> elimTy ev (f :<: Pi s t) (A e) = Just (A (s :>: e),t $$ A (ev e)) 
> import <- ElimTyRules
> elimTy _  _              _     = Nothing


\subsection{Equality and Quotation}

Testing for equality is a direct application of normalization by
evaluation\cite{dybjer:nbe, chapman:phd, dybjer:dependent_types_work}:
to compare two values, we first bring them to their normal form. Then,
it is a simple matter of syntactic equality, defined in Section
\ref{sec:syntactic_equality}, to compare the normal forms.

> equal :: (TY :>: (VAL,VAL)) -> Root -> Bool
> equal (ty :>: (v1,v2)) r = quote (ty :>: v1) r == quote (ty :>: v2) r


|quote| is a type-directed operation that returns a normal form |INTM|
by recursively evaluating the value |VAL| of type |TY|. Unless I'm
mistaken, the normal form corresponds to a |\beta|-normal |\eta|-long
form: there are no |\beta|-redexes present and all possible
|\eta|-expansions have been performed.

This is performed by two mutually recursive functions, |inQuote| and
|exQuote|:

< inQuote :: (TY :>: VAL) -> Root -> INTM
< exQuote :: NEU -> Root -> (EXTM :<: TY)

Where |inQuote| quotes values and |exQuote| quotes neutral terms. As
we are initially provided with a value, we quote it with |inQuote|, in
a fresh namespace.

> quote :: (TY :>: VAL) -> Root -> INTM
> quote vty r = inQuote vty (room r "quote")


Quoting a value consists in, if possible, $\eta$-expanding
it. Needless to say, we can always $\eta$-expand a closure. If
$\eta$-expansion has failed, there are two possible cases: either we
are quoting a neutral term, or a canonical term. In the case of
neutral term, we simply switch to |exQuote|, which is designed to
quote neutral terms.

In the case of a canonical term, we use |canTy| to check that |cv| is
of type |cty| and, more importantly, to evaluate |cty|. Then, it is
simply a matter of quoting this |type :>: val| inside the canonical
constructor, and return the fully quoted term. The reason for the
breeding of |Just| is that we are in the |Maybe| monad, and we really
want to stay in there: |canTy| asks for a |MonadPlus|. Obviously,
(hopefully) we cannot fail in this code, but we have to be
artificially cautious. Hence, this is |Just| a mess.

> inQuote :: (TY :>: VAL) -> Root -> INTM
> inQuote tyv              r | Just t    <- etaExpand tyv r = t
> inQuote (_ :>: N n)      r = N t
>     where (t :<: _) = exQuote n r
> inQuote (C cty :>: C cv) r = fromJust $ do
>     ct <- canTy (\t -> Just t) (cty :>: cv)
>     c <- traverse (\c -> Just $ inQuote c r)  ct
>     return $ C c

As mentioned above, |\eta|-expansion is the first sensible thing to do
when quoting. Sometimes it works, especially for closures and features
for which an |EtaExpand| aspect is defined. Quoting a closure is a bit
tricky: you cannot compute under a binder as you would like to. So, we
first have to generate a fresh variable |v|. Then, we apply |v| to the
function |f|, getting a value of type |t v|. At this point, we can
safely quote this term. The result is a binding of |v| in the quoted
term.

> etaExpand :: (TY :>: VAL) -> Root -> Maybe INTM
> etaExpand (C (Pi s t) :>: f) r = Just $
>   L ("" :. fresh ("" :<: s) (\v  -> inQuote (t $$ A v :>: (f $$ A v))) r)
> import <- EtaExpand
> etaExpand _                  _ = Nothing


Remember that a neutral term is either a parameter, a stuck
elimination, or a stuck operation. Hence, we consider each cases in
turn. 

> exQuote :: NEU -> Root -> (EXTM :<: TY)

Let's be clear. The code below is, in my opinion, a hack. The idea is
the following. If we are asked to quote a free variable |P| we have
introduced during |\eta|-expansion (above), we know it is bound by a
lambda: hence it needs to be turned into a bound variable |V|, with
the right De Bruijn index. If we have not introduced that free
variable, we simply return it.

Technically, we know that a free variable has been created by |quote|
if the current root and the namespace |ns| of the variable are the
same. Hence, the test |ns == r|. Then, we compute the De Bruijn index
of the bound variable by counting the number of lambdas traversed up
to now -- by looking at |j-1| in our current root |(r,j)| -- minus the
number of lambdas traversed at the time of the parameter creation,
ie. |i|. Do some math, pray, and you get the right De Bruijn index.

> exQuote (P x)       r = quop x r :<: pty x
>     where quop :: REF -> Root -> EXTM
>           quop ref@(ns := _) r = help (bwdList ns) r
>               where
>               help (ns :< (_,i)) (r,j) = if ns == r then V (j-i-1) else P ref

If an elimination is stuck, it is because the function is stuck while
the arguments are ready to go. So, we have to recursively |exQuote|
the neutral application, while |inQuote|-ing the arguments. 

> exQuote (n :$ v)    r = (n' :$ traverse inQuote e r) :<: ty'
>     where (n' :<: ty)  = exQuote n r
>           Just (e,ty') = elimTy id (N n :<: unC ty) v
>           unC :: VAL -> Can VAL
>           unC (C ty) = ty

Similarly, if an operation is stuck, this means that one of the value
passed as an argument needs to be |inQuote|-ed. So it goes. Note that
the operation itself cannot be stuck: it is a mere fully-applied
constructor.

> exQuote (op :@ vs)  r = (op :@ vals) :<: v where
>    (vs',v) = fromJust $ opTy op (\(t :>: x) -> do
>                                  return $ inQuote (t :>: x) r :=>: x) vs 
>    vals = map (\(t :=>: v) -> t) vs'



As we are in the quotation business, let us define $\beta$-quotation,
ie |bquote|. Unlike |quote|, |bquote| does not perform
$\eta$-expansion, but just brings the term in $\beta$ normal
form. Therefore, the code is much more simpler than |quote|, although
the idea is the same. 

From a technical perspective, it is important to note that we are in
|Rooty| and we don't require a specially crafted |Root| (unlike
|quote| and |quop|, as described above). Because of that, we have to
maintain the variables we have generated and to which De Bruijn index
they correspond. This is the role of the backward list of references. We let 

Note that we let the user provide an initial environment of
references: this is useful to discharge a bunch of assumptions inside
a term. The typical use-case is @Tactics.lhs:discharge@.

Apart from that, this is a standard $\beta$-quotation: 

> bquote :: Rooty m => Bwd REF -> Tm {d,VV} REF -> m (Tm {d,TT} REF)

If binded by a lambda of ours, we bound the free variables to the
(hopefully) correct lambda. We don't do anything otherwise.

> bquote  refs (P x) =
>     case x `elemIndex` refs of
>       Just i -> pure $ V i 
>       Nothing -> pure $ P x

Going under a closure is the usual story: we create a fresh variable,
evaluate the applied term, quote the result, and bring everyone under
a binding.

> bquote refs (L (H vs x t)) = 
>     (|(\t -> L (x :. t))
>       (Rooty.freshRef (x :<: undefined) 
>                       (\x -> bquote (refs :< x) 
>                                     (eval t (vs :< pval x))))|)

For the other constructors, we simply go through and do as much damage
as we can. Simple.

> bquote refs (L (K t)) = (|(L . K) (bquote refs t) |)
> bquote refs (C c) = (|C (traverse (bquote refs) c )|)
> bquote refs (N n) = (|N (bquote refs n)|)
> bquote refs (n :$ v) = (|(:$) (bquote refs n)
>                                 (traverse (bquote refs) v)|)
> bquote refs (op :@ vs) = (|(:@) (pure op)
>                                   (traverse (bquote refs) vs)|)



\subsection{Type inference}

> infer :: EXTM -> Root -> Maybe TY
> infer (P x)              r = Just (pty x)
> infer (t :$ s)           r = do
>   C ty <- infer t r
>   (s',ty') <- elimTy evTm (evTm t :<: ty) s
>   traverse id $ traverse check s' r
>   return ty'
> infer (op :@ ts)         r = do
>   (vs,v) <- opTy op (\tx@(t :>: x) -> do 
>                                       ch <- check tx r 
>                                       return $ ch :=>: evTm x) ts
>   return v
> infer (t :? ty)          r = do
>   check (SET :>: ty) r
>   let vty = evTm ty
>   check (vty :>: t) r
>   return vty
> infer _                  _ = Nothing


\subsection{Type checking}


> check :: (TY :>: INTM) -> Root -> Maybe ()
> check (C c :>: C c')        r = do
>   csp <- canTy (Just . evTm) (c :>: c')
>   return ()
> check (C (Pi s t) :>: L sc) r = do
>   Root.freshRef ("" :<: s) 
>            (\ref -> check (t $$ A (pval ref) :>: underScope sc ref)) 
>            r
> check (w :>: N n)           r = do
>   y <- infer n r
>   guard $ equal (SET :>: (w, y)) r
>   return ()
> import <- Check
> check _                     _ = Nothing




\subsection{Operators}

> import <- OpCode

> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

> import <- SugarTactics

\subsection{Equality?}

> mkEqConj :: [(TY :>: VAL,TY :>: VAL)] -> VAL
> mkEqConj ((y0 :>: t0,y1 :>: t1) : []) = eqGreen @@ [y0,t0,y1,t1]
> mkEqConj ((y0 :>: t0,y1 :>: t1) : xs) = 
>   AND (eqGreen @@ [y0,t0,y1,t1]) (mkEqConj xs)
> mkEqConj []                           = TRIVIAL

> eqGreenT :: (InTm x :>: InTm x) -> (InTm x :>: InTm x) -> InTm x
> eqGreenT (y0 :>: t0) (y1 :>: t1) = N (eqGreen :@ [y0,t0,y1,t1])

> opRunEqGreen :: [VAL] -> Either NEU VAL
> opRunEqGreen [SET,C t0,SET,C t1] = case halfZip t0' t1' of
>    Nothing -> Right ABSURD
>    Just x  -> Right $ mkEqConj (trail x)
>    where
>    Just t0' = canTy Just (Set :>: t0)
>    Just t1' = canTy Just (Set :>: t1)
> import <- OpRunEqGreen
> opRunEqGreen [C (Pi s1 t1),f1,C (Pi s2 t2),f2] = Right $
>   eval  [.s1.t1.f1.s2.t2.f2.
>         ALL (NV s1) . L $ "" :. [.x1.
>         ALL (NV s2) . L $ "" :. [.x2.
>         IMP (EQBLUE (NV s2 :>: NV x2) (NV s1 :>: NV x1))
>             (eqGreenT (t1 $# [x1] :>: f1 $# [x1]) (t2 $# [x2] :>: f2 $# [x2]))
>         ]]]
>         $ B0 :< s1 :< t1 :< f1 :< s2 :< t2 :< f2

%if False

> {-
>    ALL s1 (L (H (bwdList [s1,t1,f1,s2,t2,f2])
>                 "" 
>                 (ALL (NV 3) -- s2
>                      (L ("" 
>                          :. 
>                          (IMP (EQBLUE (NV 7 :>: NV 1)  -- s1 :>: x1
>                                       (NV 4 :>: NV 0)) -- s2 :>: x2
>                               (N (eqGreen :@ [N (V 5 :$ A NV 1), -- f1 x1
>                                               N (V 6 :$ A NV 1), -- t1 x1
>                                               N (V 2 :$ A NV 0), -- f2 x2
>                                               N (V 3 :$ A NV 0)] -- t2 x2
>                                  ))))))))
> -}

%endif

> opRunEqGreen [SET,N t0,SET,_] = Left t0
> opRunEqGreen [SET,_,SET,N t1] = Left t1
> opRunEqGreen [N y0,_,_,_] = Left y0
> opRunEqGreen [_,_,N y1,_] = Left y1
> opRunEqGreen [C y0,_,C y1,_] = Right TRIVIAL

> coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> VAL
> coerce (Pi (x1,x2) (y1,y2))    q f = 
>              eval [.x1.x2.y1.y2.q.f.
>                   (L $ "" :. [.s1.
>                     (let
>                     s2 = N (coe :@ [NV x2,NV x1,N (V q :$ Fst),NV s1])
>                     q2 = N (coh :@ [NV x2,NV x1,N (V q :$ Fst),NV s1])
>                     in
>                     N $ coe :@ [N (V y2 :$ A s2),
>                                 y1 $# [s1],
>                                 N (V q :$ A s2 :$ A (NV s1) :$ A q2),
>                                 N (V f :$ A s2)])])]
>                    (B0 :< x1 :< x2 :< y1 :< y2 :< q :< f)
> import <- Coerce
