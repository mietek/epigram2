\section{Lambda-lifting and discharging}
\label{sec:ProofState.Interface.Lifting}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.Interface.Lifting where

> import Data.Foldable

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Rules

> import ProofState.Edition.Scope

> import ProofState.Structure.Developments

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\pierre{I think that, after some clean-up, the following could well be
moved in @ProofState.Edition.Scope@}

In the following, we define 4 useful functions manipulating terms in a
context of entries. These functions provide the basic toolkit for
operations like lambda-lifting, or the manipulation of the proof
state. Therefore, this section has to be read with the tired eye of
the implementer.


\subsection{Discharging entries in a term}


The ``discharge into'' operator |(-||)| takes a list of entries and a
term, and changes the term so that parameters in the list of entries
are represented by de Brujin indices. It makes key use of the |(-||||)|
mangler.

> (-|) :: Entries -> INTM -> INTM
> es -| tm = (bwdList $ paramREFs es) -|| tm

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
>     help B0                                        B0            t = t
>     help (delta   :< EPARAM _ (x, _)  _ _)         B0            t =
>         help delta B0 (L (x :. t))
>     help (delta   :< _)                            B0            t = 
>         help delta B0 t
>     help (delnab  :< EPARAM _ (x, _)  ParamLam _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< EPARAM _ (x, _)  ParamAll _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< EPARAM _ (x, _)  ParamPi s)   (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))
>     help (delnab  :< _)                            (nabla :< _)  t = 
>         help delnab nabla t


\subsection{Binding a type}

The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Entries -> INTM -> INTM
> liftType es = liftType' (bwdList $ foldMap param es) 
>   where param (EPARAM r _ _ t) = [r :<: t]
>         param _ = []

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
$\lambda$ in the list of entries, and produces |SET| when it
encounters a $\Pi$.

> inferGoalType :: Bwd (Entry Bwd) -> INTM -> INTM
> inferGoalType B0 t = t
> inferGoalType (es :< EPARAM _ (x,_)  ParamLam  s)  t        = 
>     inferGoalType es (PI (es -| s) (L (x :. t)))
> inferGoalType (es :< EPARAM _ (x,_)  ParamAll  s)  (PRF t)  =
>     inferGoalType es (PRF (ALL (es -| s) (L (x :. t))))
> inferGoalType (es :< EPARAM _ (x,_)  ParamPi   s)  SET      = 
>     inferGoalType es SET
> inferGoalType (es :< _)                        t        = 
>     inferGoalType es t



\subsection{Discharging}

\adam{This needs to move to somewhere more sensible, out of the ProofState.}

The |dischargeLam| function discharges and $\lambda$-binds a list of references
over a term.

> dischargeLam :: Bwd REF -> INTM -> INTM
> dischargeLam bs v = wrapLambdas bs (bs -|| v)
>   where
>     wrapLambdas :: Bwd REF -> INTM -> INTM
>     wrapLambdas B0 tm = tm
>     wrapLambdas (bs :< (n := _)) tm = wrapLambdas bs (L (fst (last n) :. tm))

The |dischargeF| function discharges and binds a list of typed references over a
term, using the given |binder| function at each step. The |binder| takes a |Bool|
indicating whether the corresponding reference occurred in the original term, the
name advice for the binder, the type of the reference and the term to be bound.

> dischargeF ::  (Bool -> String -> INTM -> INTM -> INTM) ->
>                         Bwd (REF :<: INTM) -> INTM -> INTM
> dischargeF binder bs v =
>     wrapFs bs (fmap (v `contains`) bs') (bs' -|| v)
>   where
>     bs' = fmap fstEx bs
>
>     contains :: INTM -> REF -> Bool
>     contains = flip Data.Foldable.elem
>
>     wrapFs :: Bwd (REF :<: INTM) -> Bwd Bool -> INTM -> INTM
>     wrapFs B0 B0 tm = tm
>     wrapFs (bs :< ((n := _) :<: ty)) (cs :< c) tm =
>         wrapFs bs cs (binder c (fst (last n)) ty tm)

Using the above, we can easily discharge and $\forall$-bind or discharge and
$\Pi$-bind. Note that when the bound variable is not used, a |K| binder is used.
For |dischargeAll|, the initial term must be in the form |PRF q| for some
proposition |q|. 

> dischargeAll :: Bwd (REF :<: INTM) -> INTM -> INTM
> dischargeAll = dischargeF f
>   where 
>     f :: Bool -> String -> INTM -> INTM -> INTM
>     f True   x p (PRF q) = PRF (ALLV x p q)
>     f False  x p (PRF q) = PRF (ALL p (LK q))

> dischargePi :: Bwd (REF :<: INTM) -> INTM -> INTM
> dischargePi = dischargeF f
>   where
>     f :: Bool -> String -> INTM -> INTM -> INTM
>     f True   x p q = PIV x p q
>     f False  x p q = PI p (LK q)

The |dischargeAllREF| function calls |dischargeAll| on the type of a reference,
producing a reference with the same name but whose type is $\forall$-abstracted
over the list of references. This should be used with caution, as it could lead
to having two references with the same name but different types.

> dischargeAllREF :: Bwd (REF :<: INTM) -> REF :<: INTM -> REF :<: INTM
> dischargeAllREF bs ((n := DECL :<: _) :<: ty) =
>     (n := DECL :<: evTm ty') :<: ty'
>   where ty' = dischargeAll bs ty
