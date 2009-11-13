\section{Pretty-printing}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module PrettyPrint (prettyDev, prettyName, prettyRef, prettyScope, prettyTm) where

> import Data.List

> import BwdFwd
> import Developments
> import Tm

%endif

> prettyCan :: [String] -> Can (Tm {d,p} REF) -> String
> prettyCan ss Set       = "*"
> prettyCan ss (Pi s (L (K t)))  = prettyTm ss s ++ " -> " ++ prettyTm ss t
> prettyCan ss (Pi s t)  = "Pi (" ++ prettyTm ss s ++ ") (" ++ prettyTm ss t ++ ")"
> prettyCan ss (Con x)   = "Con (" ++ prettyTm ss x ++ ")"

> prettyDev :: Dev -> String
> prettyDev d = showDevAcc d 0 ""
>     where showDevAcc :: Dev -> Int -> String -> String
>           showDevAcc (B0, t, r) n acc = acc ++ "\n" ++ indent n 
>                                         ++ "Tip: " ++ prettyTip t ++ "\n" ++ indent n
>                                         ++ "Root: " ++ show r
>           showDevAcc (es :< E ref _ (Boy k), t, r) n acc = 
>               showDevAcc (es, t, r) n (
>               "\n" ++ indent n ++ "Boy " ++ show k ++ " " ++ prettyRef [] ref
>               ++ acc)
>           showDevAcc (es :< E ref _ (Girl LETG d), t, r) n acc = 
>               showDevAcc (es, t, r) n (
>               "\n" ++ indent n ++ "Girl " ++ prettyRef [] ref
>               ++ showDevAcc d (succ n) ""
>               ++ acc)
>               
>           indent n = replicate (n*4) ' '

> prettyElim :: [String] -> Elim (Tm {d,p} REF) -> String
> prettyElim ss (A t)  = prettyTm ss t
> prettyElim ss Out    = "Out"

> prettyName :: Name -> String                
> prettyName = intercalate "." . fst . unzip

> prettyRef :: [String] -> REF -> String
> prettyRef ss (ns := k :<: ty) = prettyName ns ++ prettyRKind k ++ prettyTm ss ty
>     where prettyRKind :: RKind -> String
>           prettyRKind DECL      = " : "
>           prettyRKind (DEFN v)  = " := " ++ prettyTm ss v ++ " : "
>           prettyRKind HOLE      = " := ? : "

> prettyScope :: [String] -> Scope p REF -> String
> prettyScope ss (x :. t)   = show x ++ " :. " ++ prettyTm ss t
> prettyScope ss (H g x t)  =
>     "(\\ " ++ x ++ " . " ++ prettyTm (x:ss) t ++ ")"
> prettyScope ss (K t) = prettyTm ss t

> prettyTip :: Tip -> String
> prettyTip Module           = "Module"
> prettyTip (Unknown ty)     = "? : " ++ prettyTm [] ty
> prettyTip (Defined tm ty)  = prettyTm [] tm ++ " : " ++ prettyTm [] ty

> prettyTm :: [String] -> Tm {d,p} REF -> String
> prettyTm ss (L s)       = prettyScope ss s
> prettyTm ss (C c)       = prettyCan ss c
> prettyTm ss (N n)       = prettyTm ss n
> prettyTm ss (P (ns := _))  = prettyName ns
> prettyTm ss (V i)       = ss !! i
> prettyTm ss (n :$ e)    = "(" ++ prettyTm ss n ++ " " ++ prettyElim ss e ++ ")"
> prettyTm ss (op :@ vs)  = "(" ++ opName op ++ " :@ " ++ show vs ++ ")"
> prettyTm ss (t :? y)    = "(" ++ prettyTm ss t ++ " :? " ++ prettyTm ss y ++ ")"
