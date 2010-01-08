\section{Distillation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Distiller where

> import DisplayTm
> import MissingLibrary
> import Naming
> import PrettyPrint
> import ProofState
> import Rooty
> import Rules
> import Tm

%endif


The |distill| command converts a typed INTM in the evidence language
to a term in the display language; that is, it reverses |elaborate|.

> distill :: (TY :>: INTM) -> ProofState (INDTM :=>: VAL)

> distill (C ty :>: C c)  = do
>     cc <- canTy distill (ty :>: c)
>     return ((DC $ fmap termOf cc) :=>: evTm (C c))

> distill (ty :>: l@(L sc))  = do
>     (_, s, f) <- lambdable ty `catchMaybe` ("distill: type " ++ show ty ++ " is not lambdable.")
>     root <- getDevRoot
>     tm' :=>: _ <- freshRef (fortran l :<: s) 
>         (\ref root -> putDevRoot root >> distill (f (pval ref) :>: underScope sc ref)) root
>     return $ DL (convScope sc tm')   :=>: (evTm $ L sc)
>   where
>     convScope :: Scope {TT} REF -> INDTM -> DScope REF
>     convScope (x :. _)  tm = x ::. tm
>     convScope (K _)     tm = DK tm

> distill (_ :>: N n) = do
>     (n' :<: _) <- boil n
>     return (DN n' :=>: evTm n)

> distill (ty :>: tm) = error ("distill: can't cope with\n" ++ show ty ++ "\n:>:\n" ++ show tm)


The |boil| command is the |EXTM| version of |distill|, which also yields
the type of the term. 

> boil :: EXTM -> ProofState (EXDTM :<: TY)

> boil (P s)       = return (DP s :<: pty s)

> boil (t :$ e)    = do
>     (t' :<: C ty) <- boil t
>     (e', ty') <- elimTy distill (evTm t :<: ty) e
>     return ((t' ::$ fmap termOf e') :<: ty')

> boil (op :@ ts)  = do
>     (ts', ty) <- opTy op distill ts
>     return ((op ::@ fmap termOf ts') :<: ty) 

> boil (t :? ty)    = do
>     ty'  :=>: vty  <- distill (SET :>: ty)
>     t'   :=>: _    <- distill (vty :>: t)
>     return ((t' ::? ty') :<: vty)

> boil tm = error ("boil: can't cope with " ++ show tm)