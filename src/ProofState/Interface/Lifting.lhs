\section{Lambda-lifting and discharging}
\label{sec:lifting}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.Interface.Lifting where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Rules

> import ProofState.Structure.Developments

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


In the following, we define 4 useful functions manipulating terms in a
context of entries. These functions provide the basic toolkit for
operations like lambda-lifting, or the manipulation of the proof
state. Therefore, this section has to be read with the tired eye of
the implementer.


\subsection{Discharging entries in a term}


The ``discharge into'' operator |(-|)| takes a list of entries and a term, and
changes the term so that boys in the list of entries are represented by
de Brujin indices. It makes key use of the (-||) mangler.

> (-|) :: Entries -> INTM -> INTM
> es -| tm = (bwdList $ foldMap boy es) -|| tm
>   where boy (EPARAM r _ _ _)  = [r]
>         boy _                  = []

\subsection{Binding a term}


The |parBind| function $\lambda$-binds a term over a list $\Delta$ of
entries and $\lambda$- and $\Pi$-binds over a list $\nabla$ of
entries.

> parBind ::  {- $\Delta$ :: -} Bwd (Entry Bwd) {- $\Gamma$ -} -> 
>             {- $\nabla$ :: -} Bwd (Entry Bwd) {- $\Gamma, \Delta$ -} -> 
>             INTM {- $\Gamma, \Delta, \nabla$ -} ->
>             INTM {- $\Gamma$ -}
> parBind delta nabla t = help delnab nabla (delnab -| t) where
>     delnab = delta <+> nabla
>     help B0                                     B0            t = t
>     help (delta   :< EPARAM _ (x, _)  _ _)     B0            t = help delta B0 (L (x :. t))
>     help (delta   :< _)                         B0            t = help delta B0 t
>     help (delnab  :< EPARAM _ (x, _)  LAMB _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< EPARAM _ (x, _)  ALAB _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< EPARAM _ (x, _)  PIB s)   (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))
>     help (delnab  :< _)                         (nabla :< _)  t = help delnab nabla t


\subsection{Binding a type}

The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Entries -> INTM -> INTM
> liftType es = liftType' (bwdList $ foldMap boy es) 
>   where boy (EPARAM r _ _ t) = [r :<: t]
>         boy _ = []

> liftType' :: Bwd (REF :<: INTM) -> INTM -> INTM
> liftType' rtys t = pis rs tys (rs -|| t)
>   where
>     (rs, tys) = unzipBwd rtys
>
>     unzipBwd B0 = (B0, B0)
>     unzipBwd (rtys :< (r :<: ty)) = (rs :< r, tys :< ty)
>       where (rs, tys) = unzipBwd rtys

>     pis B0 B0 t = t
>     pis (rs :< r) (tys :< ty)  t = pis rs tys (PI (rs -|| ty) (L ((fst . last . refName $ r) :. t)))



\subsection{Making a type out of a goal}

The |inferGoalType| function $\Pi$-binds the type when it encounters a
$\lambda$-boy in the list of entries, and produces |SET| when it
encounters a $\Pi$-boy.

> inferGoalType :: Bwd (Entry Bwd) -> INTM -> INTM
> inferGoalType B0 t = t
> inferGoalType (es :< EPARAM _ (x,_)  LAMB  s)  t        = 
>     inferGoalType es (PI (es -| s) (L (x :. t)))
> inferGoalType (es :< EPARAM _ (x,_)  ALAB  s)  (PRF t)  =
>     inferGoalType es (PRF (ALL (es -| s) (L (x :. t))))
> inferGoalType (es :< EPARAM _ (x,_)  PIB   s)  SET      = 
>     inferGoalType es SET
> inferGoalType (es :< _)                        t        = 
>     inferGoalType es t



\subsection{Horrible horrible discharging}

\question{This needs lots of refactoring.}

The |dischargeLots| function discharges and $\lambda$-binds a list of
references over a |VAL|.

> dischargeLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargeLots bs v = do
>     v' <- bquote bs v
>     return (evTm (wrapLambdas bs v'))
>   where
>     wrapLambdas :: Bwd REF -> INTM -> INTM
>     wrapLambdas B0 tm = tm
>     wrapLambdas (bs :< (n := _)) tm = wrapLambdas bs (L (fst (last n) :. tm))


The |dischargeFLots| function discharges and binds a list of
references over a |VAL|. The |binder| is informed whether or not the
variable is actually used.

> dischargeFLots :: (NameSupplier m) => 
>                   (Bool -> String -> INTM -> INTM -> INTM) ->
>                   Bwd REF -> VAL -> m VAL
> dischargeFLots binder bs v = do
>     temp <- bquote B0 v
>     let cs = fmap (contains temp) bs
>     v' <- bquote bs v
>     v'' <- wrapFs bs cs v'
>     return (evTm v'')
>   where
>     wrapFs :: (NameSupplier m) => Bwd REF -> Bwd Bool -> INTM -> m INTM
>     wrapFs B0 _ tm = return tm
>     wrapFs (bs :< (n := _ :<: ty)) (cs :< c) tm = do
>         ty' <- bquote B0 ty
>         wrapFs bs cs (binder c (fst (last n)) ty' tm)
>     contains :: INTM -> REF -> Bool
>     contains tm ref = Data.Foldable.any (== ref) tm

Hence, we can easily discharge then $\forall$-bind or discharge then
$\Pi$-bind. Note that when the bound variable is not used, a |K|
binder is used.

> dischargeAllLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargeAllLots = dischargeFLots f
>   where 
>     f :: Bool -> String -> INTM -> INTM -> INTM
>     f True   x p (PRF q) = PRF (ALLV x p q)
>     f False  x p (PRF q) = PRF (ALL p (LK q))
>
> dischargePiLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargePiLots = dischargeFLots f
>   where
>     f :: Bool -> String -> INTM -> INTM -> INTM
>     f True   x p q = PIV x p q
>     f False  x p q = PI p (LK q)


The |dischargeRef| function calls |dischargeLots| on the type of a reference.

> dischargeRef :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRef bs (n := DECL :<: ty) = do
>     ty' <- dischargeLots bs ty
>     return (n := DECL :<: ty')


The |dischargeRefAlls| function calls |dischargeAllLots| on the type of a reference.

> dischargeRefAlls :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRefAlls bs (n := DECL :<: ty) = do
>     ty' <- dischargeAllLots bs ty
>     return (n := DECL :<: ty')

The |dischargeRefPis| function calls |dischargePiLots| on the type of a reference.

> dischargeRefPis :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRefPis bs (n := DECL :<: ty) = do
>     ty' <- dischargePiLots bs ty
>     return (n := DECL :<: ty')
