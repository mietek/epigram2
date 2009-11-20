\section{Pretty-printing}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module PrettyPrint (pretty, prettyDev, prettyName, prettyRef, prettyVAL, printDev) where

> import Data.List
> import Text.PrettyPrint.HughesPJ

> import BwdFwd hiding ((<+>))
> import qualified BwdFwd ((<+>))
> import Developments
> import Features
> import Tm hiding (($$))

%endif

The following uses the |HughesPJ| pretty-printing combinators.
\question{Is passing a list of |String|s the best way to handle scopes?}

> prettyBinder :: String -> Doc
> prettyBinder ""  = text "\"\""
> prettyBinder x   = text x

> prettyCan :: ENV -> Can (Tm {d, p} REF) -> Doc
> prettyCan e Set       = text "*"
> prettyCan e (Pi s (L (K t)))  = parens (sep [pretty e s <+> text "->", pretty e t])
> prettyCan e (Pi s (L (x :. t))) = parens (sep [
>     parens (prettyBinder x <+> text ":" <+> pretty e s) <+> text "->", pretty e t])
> prettyCan e (Pi s t)  = text "Pi" <+> (parens (pretty e s) $$ parens (pretty e t))
> prettyCan e (Con x)   = pretty e x
> import <- CanPretty
> prettyCan e can       = quotes . text .show $ can

> prettyDev :: Dev -> Doc
> prettyDev (es, t, r) = prettyEntries es
>                          $$ text "Tip:" <+> prettyTip t
>                          $$ text "Root:" <+> text (show r)
>     where prettyEntries :: Bwd Entry -> Doc
>           prettyEntries B0 = empty
>           prettyEntries (es :< E ref _ (Boy k)) = prettyEntries es 
>               $$ text "Boy" <+> text (show k) <+> prettyRef B0 ref
>           prettyEntries (es :< E ref _ (Girl LETG d)) = prettyEntries es
>               $$ text "Girl" <+> prettyRef B0 ref $$ nest 4 (prettyDev d)

> prettyElim :: ENV -> Elim (Tm {d, p} REF) -> Doc
> prettyElim e (A t)  = pretty e t
> prettyElim e Out    = text "Out"
> import <- ElimPretty
> prettyElim e elim   = quotes . text . show $ elim

> prettyName :: Name -> String                
> prettyName = intercalate "." . fst . unzip

> prettyRef :: ENV -> REF -> Doc
> prettyRef ss (ns := k :<: ty) = text (prettyName ns) <+> prettyRKind k <+> prettyVAL ss ty
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> prettyVAL ss v <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyScope :: ENV -> Scope p REF -> Doc
> prettyScope ss (x :. t)   = parens (prettyBinder x <+> text ":." <+> prettyTm (ss :< SET) t)
> prettyScope ss (H g x t)  = parens (text "\\" <> prettyBinder x <> text "."
>     <+> prettyTm (ss BwdFwd.<+> g :< SET) t)
> prettyScope ss (K t) = parens (text "\\_." <+> pretty ss t)

> prettyTip :: Tip -> Doc
> prettyTip Module           = text "Module"
> prettyTip (Unknown ty)     = text "? :" <+> prettyVAL B0 ty
> prettyTip (Defined tm ty)  = pretty B0 tm <+> text ":" <+> prettyVAL B0 ty

> prettyVAL :: ENV -> Tm {d, VV} REF -> Doc
> prettyVAL = pretty

> prettyTm :: ENV -> Tm {d, TT} REF -> Doc
> prettyTm = pretty

> pretty :: ENV -> Tm {d, p} REF -> Doc
> pretty e (L s)          = prettyScope e s
> pretty e (C c)          = prettyCan e c
> pretty e (N n)          = pretty e n
> pretty e (P (ns := _))  = text (prettyName ns)
> pretty e (V i)          = char 'V' <> int i {- <> brackets (text . take 10 . show $ e !. i) -}
> pretty e (op :@ vs)     = parens (text (opName op) 
>     <+> sep (punctuate comma (map (pretty e) vs)))
> pretty e (n :$ el)      = parens (pretty e n <+> prettyElim e el)
> pretty e (t :? y)       = parens (pretty e t <+> text ":" <+> pretty e y)

> printDev :: Dev -> IO ()
> printDev = putStrLn . show . prettyDev


> import <- Pretty