\section{Operators and primitives}
\label{sec:Evidences.Operators}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.Operators where

> import Control.Applicative

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import {-# SOURCE #-} Evidences.Eval
> import Evidences.OperatorDSL
> import {-# SOURCE #-} Evidences.DefinitionalEquality
> import {-# SOURCE #-} Evidences.PropositionalEquality
> import {-# SOURCE #-} Evidences.BetaQuotation

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Features.Features ()

%endif


In this section, we weave some She aspects. In particular, we bring
inside @Rules.lhs@ the |operators| defined by feature files,
along with any auxiliary code.

> operators :: [Op]
> operators = (
>   import <- Operators
>   [])

> import <- OpCode
> import <- RulesCode

The list of |primitives| includes axioms and fundamental definitions provided 
by the |Primitives| aspect, plus a reference corresponding to each operator.

> primitives :: [(String, REF)]
> primitives = map (\op -> (opName op, mkRef op)) operators ++ (
>     import <- Primitives
>     [])
>   where
>     mkRef :: Op -> REF
>     mkRef op = [("Operators",0),(opName op,0)] := (DEFN opEta :<: opTy)
>       where
>         opTy = pity (opTyTel op) (((B0 :<  ("Operators",0) :< 
>                                            (opName op,0) :<
>                                            ("opTy",0)), 0) :: NameSupply)
>         ari = opArity op
>         args = map NV [(ari-1),(ari-2)..0]
>         names = take (ari-1) (map (\x -> [x]) ['b'..])
>         opEta = L $ "a" :. Prelude.foldr (\s x -> L (s :. x)) (N $ op :@ args) names
>

We can look up the primitive reference corresponding to an operator using
|lookupOpRef|. This ensures we maintain sharing of these references.

> lookupOpRef :: Op -> REF
> lookupOpRef op = case lookup (opName op) primitives of
>     Just ref  -> ref
>     Nothing   -> error $ "lookupOpRef: missing operator primitive " ++ show op

> pity :: NameSupplier m => TEL TY -> m TY
> pity (Target t)       = return t
> pity (x :<: s :-: t)  = do
>   freshRef  (x :<: error "pity': type undefined")
>             (\xref -> do
>                t <- pity $ t (pval xref)
>                t <- bquote (B0 :< xref) t
>                return $ PI s (L $ x :. t))
