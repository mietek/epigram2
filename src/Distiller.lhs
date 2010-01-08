\section{Distillation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Distiller where

> import BwdFwd
> import Developments
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
It performs christening at the same time.

> distill :: Entries -> (TY :>: INTM) -> ProofState (InDTm String :=>: VAL)

> distill es (C ty :>: C c)  = do
>     cc <- canTy (distill es) (ty :>: c)
>     return ((DC $ fmap termOf cc) :=>: evTm (C c))

> distill es (ty :>: l@(L sc))  = do
>     (k, s, f) <- lambdable ty `catchMaybe` ("distill: type " ++ show ty ++ " is not lambdable.")
>     root <- getDevRoot
>     tm' :=>: _ <- freshRef (fortran l :<: s) (\ref root -> do
>         putDevRoot root
>         distill (es :< E ref (lastName ref) (Boy k) (error "distill: boy type undefined")) (f (pval ref) :>: underScope sc ref)
>       ) root
>     return $ DL (convScope sc tm')   :=>: (evTm $ L sc)
>   where
>     convScope :: Scope {TT} REF -> InDTm String -> DScope String
>     convScope (x :. _)  tm = x ::. tm
>     convScope (K _)     tm = DK tm

> distill es (_ :>: N n) = do
>     (n' :<: _) <- boil es n
>     return (DN n' :=>: evTm n)

> distill _ (ty :>: tm) = error ("distill: can't cope with\n" ++ show ty ++ "\n:>:\n" ++ show tm)


The |boil| command is the |EXTM| version of |distill|, which also yields
the type of the term. 

> boil :: Entries -> EXTM -> ProofState (ExDTm String :<: TY)

> boil es (P s)       = do
>     aus <- getAuncles
>     me <- getMotherName
>     return (mangleP (aus <+> es) me B0 (refName s) [] :<: pty s)

> boil es (t :$ e)    = do
>     (t' :<: C ty) <- boil es t
>     (e', ty') <- elimTy (distill es) (evTm t :<: ty) e
>     return ((t' ::$ fmap termOf e') :<: ty')

> boil es (op :@ ts)  = do
>     (ts', ty) <- opTy op (distill es) ts
>     return ((op ::@ fmap termOf ts') :<: ty) 

> boil es (t :? ty)    = do
>     ty'  :=>: vty  <- distill es (SET :>: ty)
>     t'   :=>: _    <- distill es (vty :>: t)
>     return ((t' ::? ty') :<: vty)

> boil _ tm = error ("boil: can't cope with " ++ show tm)