\section{Lambda-lifting and discharging}
\label{sec:lifting}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.Lifting where

> import Control.Applicative
> import Control.Monad.Identity

> import Kit.BwdFwd

> import Evidences.Tm
> import Evidences.Mangler

> import ProofState.Developments

%endif




The |(-||)| operator takes a list of entries and a term, and changes the term
so that boys in the list of entries are represented by de Brujin indices.

> (-|) :: Bwd (Entry Bwd) -> INTM -> INTM
> es -| t = disMangle es 0 %% t
>   where
>     disMangle :: Bwd (Entry Bwd) -> Int -> Mangle Identity REF REF
>     disMangle ys i = Mang
>       {  mangP = \ x ies -> (|(h ys x i $:$) ies|)
>       ,  mangV = \ i ies -> (|(V i $:$) ies|)
>       ,  mangB = \ _ -> disMangle ys (i + 1)
>       }
>     h B0                        x i  = P x
>     h (ys :< E y _ (Boy _) _)     x i
>       | x == y     = V i
>       | otherwise  = h ys x (i + 1)
>     h (ys :< E _ _ (Girl _ _) _)  x i = h ys x i
>     h (ys :< M _ _) x i = h ys x i

The |parBind| function $\lambda$-binds over a list $\Delta$ of entries and
$\lambda$- and $\Pi$-binds over a list $\nabla$.

> parBind ::  {- $\Delta$ :: -} Bwd (Entry Bwd) {- $\Gamma$ -} -> 
>             {- $\nabla$ :: -} Bwd (Entry Bwd) {- $\Gamma, \Delta$ -} -> 
>             INTM {- $\Gamma, \Delta, \nabla$ -} ->
>             INTM {- $\Gamma$ -}
> parBind delta nabla t = help delnab nabla (delnab -| t) where
>     delnab = delta <+> nabla
>     help B0                                     B0            t = t
>     help (delta   :< E _ (x, _)  (Boy _) _)     B0            t = help delta B0 (L (x :. t))
>     help (delta   :< _)                         B0            t = help delta B0 t
>     help (delnab  :< E _ (x, _)  (Boy LAMB) _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Boy ALAB) _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Boy PIB) s)   (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))
>     help (delnab  :< _)                         (nabla :< _)  t = help delnab nabla t



The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Bwd (Entry Bwd) -> INTM -> INTM
> liftType es t = pis es (es -| t) where
>   pis B0 t = t
>   pis (es :< E _ (x,_)  (Boy _)     s)  t = pis es (PI (es -| s) (L (x :. t)))
>   pis (es :< _)                         t = pis es t


The |inferGoalType| function $\Pi$-binds the type when it encounters a $\lambda$-boy
in the list of entries, and produces |SET| when it encounters a $\Pi$-boy.

> inferGoalType :: Bwd (Entry Bwd) -> INTM -> INTM
> inferGoalType B0 t = t
> inferGoalType (es :< E _ (x,_)  (Boy LAMB)  s)  t        = inferGoalType es (PI (es -| s) (L (x :. t)))
> inferGoalType (es :< E _ (x,_)  (Boy ALAB)  s)  (PRF t)  = inferGoalType es (PRF (ALL (es -| s) (L (x :. t))))
> inferGoalType (es :< E _ (x,_)  (Boy PIB)   s)  SET      = inferGoalType es SET
> inferGoalType (es :< _)                         t        = inferGoalType es t

