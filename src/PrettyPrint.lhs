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

> type PrettyENV = Bwd (Either String VAL)

The following uses the |HughesPJ| pretty-printing combinators.
\question{Is passing a list of |String|s the best way to handle scopes?}

> renameBinder :: PrettyENV -> String -> String
> renameBinder e ""  = '_': (show (bwdLength e))
> renameBinder _ x   = x

> prettyCan :: PrettyENV -> Can (Tm {d, p} REF) -> Doc
> prettyCan e Set       = text "*"
> prettyCan e (Pi s (L (K t)))  = parens (sep [pretty e s <+> text "->", pretty e t])
> prettyCan e (Pi s (L (x :. t))) = let y = renameBinder e x in
>     parens (sep [parens (text y <+> text ":" <+> pretty e s) <+> text "->", pretty (e :< Left y) t])
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
>               $$ text "Boy" <+> prettyBKind k <+> prettyRef B0 ref
>           prettyEntries (es :< E ref _ (Girl LETG d)) = prettyEntries es
>               $$ text "Girl" <+> prettyRef B0 ref $$ nest 4 (prettyDev d)
>           
>           prettyBKind :: BoyKind -> Doc
>           prettyBKind LAMB     = text "Lamb"
>           prettyBKind (PIB t)  = text "Pi"


> prettyElim :: PrettyENV -> Elim (Tm {d, p} REF) -> Doc
> prettyElim e (A t)  = pretty e t
> prettyElim e Out    = text "Out"
> import <- ElimPretty
> prettyElim e elim   = quotes . text . show $ elim

> prettyName :: Name -> String                
> prettyName = intercalate "." . fst . unzip

> prettyRef :: PrettyENV -> REF -> Doc
> prettyRef e (ns := k :<: ty) = text (prettyName ns) <+> prettyRKind k <+> prettyVAL e ty
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> prettyVAL e v <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyScope :: PrettyENV -> Scope p REF -> Doc
> prettyScope e (x :. t)   = let y = renameBinder e x in
>     parens (text y <+> text ":." <+> prettyTm (e :< Left y) t)
> prettyScope e (H g x t)  = let y = renameBinder e x in
>     parens (text "\\" <> text y <> text "." <+> prettyTm (e BwdFwd.<+> (fmap Right g) :< Left y) t)
> prettyScope e (K t) = parens (text "\\_." <+> pretty e t)

> prettyTip :: Tip -> Doc
> prettyTip Module                    = text "Module"
> prettyTip (Unknown (_ :=>: ty))     = text "? :" <+> prettyVAL B0 ty
> prettyTip (Defined tm (_ :=>: ty))  = pretty B0 tm <+> text ":" <+> prettyVAL B0 ty

> prettyVAL :: PrettyENV -> Tm {d, VV} REF -> Doc
> prettyVAL = pretty

> prettyTm :: PrettyENV -> Tm {d, TT} REF -> Doc
> prettyTm = pretty

> pretty :: PrettyENV -> Tm {d, p} REF -> Doc
> pretty e (L s)          = prettyScope e s
> pretty e (C c)          = prettyCan e c
> pretty e (N n)          = pretty e n
> pretty e (P (ns := _))  = text (prettyName ns)
> pretty e (V i)          = case e !. i of
>                             Left s   -> text s
>                             Right v  -> char 'V' <> int i
> pretty e (op :@ vs)     = parens (text (opName op) 
>     <+> sep (punctuate comma (map (pretty e) vs)))
> pretty e (n :$ el)      = parens (pretty e n <+> prettyElim e el)
> pretty e (t :? y)       = parens (pretty e t <+> text ":" <+> pretty e y)

> printDev :: Dev -> IO ()
> printDev = putStrLn . show . prettyDev


> import <- Pretty