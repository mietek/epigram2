\section{Pretty-printing}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module PrettyPrint (pretty, prettyDev, prettyName, prettyRef, prettyTm, printDev) where

> import Data.List
> import Text.PrettyPrint.HughesPJ

> import BwdFwd hiding ((<+>))
> import Developments
> import Features
> import Tm hiding (($$))

%endif

The following uses the |HughesPJ| pretty-printing combinators.
\question{Is passing a list of |String|s the best way to handle scopes?}

> prettyBinder :: [String] -> String -> String
> prettyBinder ss  ""  = '_' : (show (length ss))
> prettyBinder _   x   = x

> prettyCan :: [String] -> Can (Tm {d,p} REF) -> Doc
> prettyCan ss Set       = text "*"
> prettyCan ss (Pi s (L (K t)))  = prettyTm ss s <+> text "->" <+> prettyTm ss t
> prettyCan ss (Pi s t)  = text "Pi" <+> parens (prettyTm ss s) <+> parens (prettyTm ss t)
> prettyCan ss (Con x)   = prettyTm ss x
> import <- CanPretty
> prettyCan ss c         = quotes . text .show $ c

> prettyDev :: Dev -> Doc
> prettyDev (es, t, r) = prettyEntries es
>                          $$ text "Tip:" <+> prettyTip t
>                          $$ text "Root:" <+> text (show r)
>     where prettyEntries :: Bwd Entry -> Doc
>           prettyEntries B0 = empty
>           prettyEntries (es :< E ref _ (Boy k)) = prettyEntries es 
>               $$ text "Boy" <+> text (show k) <+> prettyRef [] ref
>           prettyEntries (es :< E ref _ (Girl LETG d)) = prettyEntries es
>               $$ text "Girl" <+> prettyRef [] ref $$ nest 4 (prettyDev d)

> prettyElim :: [String] -> Elim (Tm {d,p} REF) -> Doc
> prettyElim ss (A t)  = prettyTm ss t
> prettyElim ss Out    = text "Out"
> import <- ElimPretty
> prettyElim ss e      = quotes . text . show $ e

> prettyName :: Name -> String                
> prettyName = intercalate "." . fst . unzip

> prettyRef :: [String] -> REF -> Doc
> prettyRef ss (ns := k :<: ty) = text (prettyName ns) <+> prettyRKind k <+> prettyTm ss ty
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> prettyTm ss v <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyScope :: [String] -> Scope p REF -> Doc
> prettyScope ss (x :. t)   = prettyTm ((prettyBinder ss x):ss) t
> prettyScope ss (H g x t)  = let x' = prettyBinder ss x in
>     parens (text "\\" <+> text x' <+> text "->" <+> prettyTm (x':ss) t)
> prettyScope ss (K t) = prettyTm ss t

> prettyTip :: Tip -> Doc
> prettyTip Module           = text "Module"
> prettyTip (Unknown ty)     = text "? :" <+> prettyTm [] ty
> prettyTip (Defined tm ty)  = prettyTm [] tm <+> text ":" <+> prettyTm [] ty

> prettyTm :: [String] -> Tm {d,p} REF -> Doc
> prettyTm ss (L s)          = prettyScope ss s
> prettyTm ss (C c)          = prettyCan ss c
> prettyTm ss (N n)          = prettyTm ss n
> prettyTm ss (P (ns := _))  = text (prettyName ns)
> prettyTm ss (V i)          = if length ss > i then text (ss !! i) else text "_?" <> int i
> prettyTm ss (op :@ vs)     = parens (text (opName op) 
>     <+> sep (punctuate comma (map (prettyTm ss) vs)))
> prettyTm ss (n :$ e)       = parens (prettyTm ss n <+> prettyElim ss e)
> prettyTm ss (t :? y)       = parens (prettyTm ss t <+> text ":" <+> prettyTm ss y)

> pretty = prettyTm []

> printDev :: Dev -> IO ()
> printDev = putStrLn . show . prettyDev