\section{Matching}
\label{sec:Tactics.Matching}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards, FlexibleContexts #-}

> module Tactics.Matching where

> import Prelude hiding (any, elem, exp)

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Error
> import Data.Foldable
> import Data.Maybe

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.TypeChecker
> import Evidences.TypeCheckRules
> import Evidences.ErrorHandling

> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Interface

> import Tactics.Unification

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

A \emph{matching substitution} is a list of references with their values, if any.

> type MatchSubst = Bwd ((Int, String, TY), Maybe EXP)

It is easy to decide if a reference is an element of such a substitution:

> elemSubst :: (Int, String, TY) -> MatchSubst -> Bool
> elemSubst (l,_,_) = any ((\(l',_,_) -> l == l') . fst)

When inserting a new reference-value pair into the substitution, we ensure that
it is consistent with any value already given to the reference.

> insertSubst :: (Applicative m, MonadError StackError m) => 
>                Int -> (Int, String, TY) -> EXP -> StateT MatchSubst m ()
> insertSubst lev a@(l,x,ty) t = get >>= flip help F0
>   where
>     help :: (Applicative m, MonadError StackError m) => 
>             MatchSubst -> Fwd ((Int, String, TY), Maybe EXP) -> StateT MatchSubst m ()
>     help B0 fs = error "insertSubst: reference not found!"
>     help (rs :< (b@(l',x',ty'), m)) fs | l == l' = case m of
>         Nothing  -> put (rs :< (a, Just t) <>< fs)
>         Just u   -> if (equal lev (ty :>: (t, u))) 
>                     then put (rs :< (b, m) <>< fs)
>                     else throwError' $ err "Multiple Solutions to matching problem"
>     help (rs :< (y, m)) fs = help rs ((y, m) :> fs)


The matching commands, defined below, take a matching substitution (initially
with no values for the references) and a pair of objects. The references must
only exist in the first object, and each reference may only depend on those
before it (in the usual telescopic style). Each command will produce an updated
substitution, potentially with more references defined.

Note that the resulting values may contain earlier references that need to be
substituted out. Any references left with no value at the end are unconstrained
by the matching problem.

The |matchValue| command requires the type of the values to be pushed in.
It expands elements of $\Pi$-types by applying them to fresh references,
which must not occur in solution values (this might otherwise happen when given
a higher-order matching problem with no solutions). The fresh references are
therefore collected in a list and |checkSafe| (defined below) is called to
ensure none of the unsafe references occur.

\adam{This is broken, because it assumes all eliminators are injective (including
projections). If you do something too complicated, it may end up matching
references with things of the wrong type. A cheap improvement would be to check
types before calling |insertSubst|, thereby giving a sound but incomplete matching
algorithm. Really we should do proper higher-order matching.} 

> matchValue :: (Applicative m, MonadError StackError m) => 
>               Int -> Bwd (Int, String, TY) -> TY :>: (VAL, VAL) -> StateT MatchSubst m ()
> matchValue lev zs (ty :>: (P x :$ B0, t)) = do
>     rs <- get
>     if x `elemSubst` rs
>         then  lift (checkSafe lev zs (ty :>: t)) >> insertSubst lev x (exp t)
>         else  matchValue' lev zs (ev ty :>: (P x :$ B0, t))
> matchValue lev zs (ty :>: vv) = matchValue' lev zs (ev ty :>: vv)



> matchValue' :: (Applicative m, MonadError StackError m) => 
>                Int -> Bwd (Int, String, TY) -> VAL :>: (VAL, VAL) -> StateT MatchSubst m ()

> matchValue' lev zs (PI s t :>: (v, w)) = do
>     rs <- get
>     rs' <- lift $ do
>         let lxty = (lev, "expand", s)
>         let p = P lxty :$ B0
>         execStateT (matchValue (lev+1) (zs :< lxty) (t $$ A p :>: (v $$ A p, w $$ A p))) rs
>     put rs'

> matchValue' lev zs (cty :- asty :>: (cs :- ass, ct :- tas)) | cs == ct = 
>   matchCan lev zs (fromJust (canTy ((cty, asty) :>: cs)) :>: (ass, tas))

> matchValue' lev zs (cty :- asty :>: (cs :- ass, ct :- tas)) = 
>     throwError' $ err "matchValue: unmatched constructors!"

> matchValue' lev zs (_ :>: (P (l,n,_T) :$ as, hb :$ bs)) = do
>     rs <- get
>     let mabs = trail $ bwdZipWith halfZip as bs 
>     ab <- case sequence mabs of
>       Nothing -> throwError' $ err "matchValue: mismatched Elim"
>       Just ab -> return ab
>     matchSpine lev zs (_T :>: P (l, n, _T) :$ B0) ab
>     if ((l,n,_T) `elemSubst` rs) 
>      then do
>       lift $ checkSafe lev zs (_T :>: hb :$ B0)
>       insertSubst lev (l, n, _T) (exp (hb :$ B0))
>       return ()
>      else case hb of 
>       P (l',_,_) -> if l == l' then return () else throwError' (err n)

> matchValue' lev zs (_ :>: ((D adef) :$ as, (D bdef:$ bs))) |
>   adef == bdef = do  
>     let mabs = trail $ bwdZipWith halfZip as bs
>     ab <- case sequence mabs of
>       Nothing -> throwError' $ err "matchValue: mismatched Elim"
>       Just ab -> return ab
>     matchSpine lev zs (defTy adef :>: def adef) ab     


> matchValue' lev zs (ty :>: (v, w)) | (equal lev (exp ty :>: (exp v, exp w))) = return ()

> matchValue' _ _ _ = throwError' $ err "matchValue' flail"


> matchCan :: (Applicative m, MonadError StackError m) => 
>             Int -> Bwd (Int, String, TY) -> 
>             VAL :>: ([EXP], [EXP]) -> StateT MatchSubst m ()
> matchCan lev zs (ONE :>: ([],[])) = return ()
> matchCan lev zs (SIGMA s t :>: (a : as, b : bs)) = do
>   let bv = ev b
>   matchValue lev zs (s :>: (ev a, bv))
>   matchCan lev zs (ev t $$. bv :>: (as, bs))

> matchSpine :: (Applicative m, MonadError StackError m) => 
>               Int -> Bwd (Int, String, TY) -> (TY :>: EXP) -> 
>               [Elim (EXP, EXP)] -> StateT MatchSubst m ()
> matchSpine l zs (ty :>: e) [] = return ()
> matchSpine l zs (ty :>: e) (A (a,b) : ab) = case lambdable (ev ty) of
>   Just (_,s,t) -> do
>     matchValue l zs (s :>: (ev a, ev b))
>     matchSpine l zs (t a :>: e $$. a) ab
> matchSpine l zs (ty :>: e) (Hd : ab) = case projable (ev ty) of
>   Just (s,t) -> matchSpine l zs (s :>: e $$ Hd) ab
> matchSpine l zs (ty :>: e) (Tl : ab) = case projable (ev ty) of
>   Just (s,t) -> matchSpine l zs (t (e $$ Hd) :>: (e $$ Tl)) ab
>  

Need to add rulez for Equalidee.

As noted above, fresh references generated when expanding $\Pi$-types must not
occur as solutions to matching problems. The |checkSafe| function throws an
error if any of the references occur in the value.

> checkSafe :: (Applicative m, MonadError StackError m) => 
>              Int -> Bwd (Int, String, TY) -> (TY :>: VAL) -> m ()
> checkSafe lev zs (ty :>: t)  | 
>   any (\(l,_,_) -> occurs lev Nothing [l] (ty :>: exp t)) zs  = throwError' $ err "checkSafe: unsafe!"
>                              | otherwise          = return ()


For testing purposes, we define a @match@ tactic that takes a telescope of
parameters to solve for, a neutral term for which those parameters are in scope,
and another term of the same type. It prints out the resulting substitution.
(See Cochon.Cochon.lhs)


