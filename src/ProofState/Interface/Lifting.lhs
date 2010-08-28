\section{Lambda-lifting and discharging}
\label{sec:ProofState.Interface.Lifting}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.Interface.Lifting where

> import Data.Foldable

> import Evidences.Tm
> import Evidences.Mangler

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
>     help (delta   :< EPARAM _ (x, _)  _ _ _)       B0            t =
>         help delta B0 (L (x :. t))
>     help (delta   :< _)                            B0            t = 
>         help delta B0 t
>     help (delnab  :< EPARAM _ (x, _)  ParamLam _ _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< EPARAM _ (x, _)  ParamAll _ _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< EPARAM _ (x, _)  ParamPi s _)   (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))
>     help (delnab  :< _)                            (nabla :< _)  t = 
>         help delnab nabla t


\subsection{Binding a type}

The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Entries -> INTM -> INTM
> liftType es = liftType' (bwdList $ foldMap param es) 
>   where param (EPARAM r _ _ t _) = [r :<: t]
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
> inferGoalType (es :< EPARAM _ (x,_)  ParamLam  s _)  t        = 
>     inferGoalType es (PI (es -| s) (L (x :. t)))
> inferGoalType (es :< EPARAM _ (x,_)  ParamAll  s _)  (PRF t)  =
>     inferGoalType es (PRF (ALL (es -| s) (L (x :. t))))
> inferGoalType (es :< EPARAM _ (x,_)  ParamPi   s _)  SET      = 
>     inferGoalType es SET
> inferGoalType (es :< _)                        t        = 
>     inferGoalType es t