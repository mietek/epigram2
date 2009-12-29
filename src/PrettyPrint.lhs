\section{Pretty-printing}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, GADTs #-}

> module PrettyPrint (pretty, prettyDev, prettyModule,
>                     prettyREF, prettyVAL, prettyINTM) where

> import Data.Foldable
> import Data.List
> import Text.PrettyPrint.HughesPJ

> import BwdFwd hiding ((<+>))
> import qualified BwdFwd ((<+>))
> import Developments
> import Features
> import Naming
> import Root
> import Rules
> import Tm hiding (($$))

%endif

The following uses the |HughesPJ| pretty-printing combinators. We define how to
pretty-print everything defined in the Core chapter here, and provide she aspects
to allow extra canonical terms and eliminators to be pretty-printed.

> prettyCan :: Can (Tm {d, p} String) -> Doc
> prettyCan Set       = text "*"
> prettyCan (Pi s (L (K t)))  = parens (sep [pretty s <+> text "->", pretty t])
> prettyCan (Pi s (L (H B0 x t)))  = 
>     parens (sep [parens (text x <+> text ":" <+> pretty s) <+> text "->", pretty t])
> prettyCan (Pi s (L (x :. t))) = 
>     parens (sep [parens (text x <+> text ":" <+> pretty s) <+> text "->", pretty t])
> prettyCan (Pi s t)  = parens (text "Pi" <+> pretty s <+> pretty t)
> prettyCan (Con x)   = text "@" <+> pretty x
> import <- CanPretty
> prettyCan can       = quotes . text .show $ can

> prettyModule :: Entries -> Name -> Dev Bwd -> Doc
> prettyModule aus me (B0, _, _) = empty
> prettyModule aus me dev = prettyDev aus me dev

> prettyDev :: Entries -> Name -> Dev Bwd -> Doc
> prettyDev gaus me (B0, Module,  _) = text "[]"
> prettyDev gaus me (B0, t,       _) = text ":=" <+> prettyTip gaus me t
> prettyDev gaus me dev@(es, t, r) =
>     lbrack <+> prettyEntries es aus $$ rbrack 
>     <+> prettyTip aus me t
>   where
>     aus = gaus BwdFwd.<+> es
>
>     prettyEntries :: Entries -> Entries -> Doc
>
>     prettyEntries (es' :< E ref _ (Boy k) _) (aus' :< _) =
>         prettyEntries es' aus'
>         $$ prettyBKind k (prettyRef aus me r ref) 
>                                          
>     prettyEntries (es' :< e) (aus' :< _) = 
>         prettyEntries es' aus'
>         $$ sep [text (christenName aus me (entryName e)),
>                 nest 2 (prettyDev aus' (entryName e) (entryDev e)) <+> semi]
>
>     prettyEntries B0 _ = empty
>
>     prettyBKind :: BoyKind -> Doc -> Doc
>     prettyBKind LAMB  d = text "\\" <+> d <+> text "->"
>     prettyBKind ALAB  d = text "\\" <+> d <+> text "=>"
>     prettyBKind PIB   d = parens d <+> text "->"


> prettyElim :: Elim (Tm {d, p} String) -> Doc
> prettyElim (A t)  = pretty t
> prettyElim Out    = text "Out"
> import <- ElimPretty
> prettyElim elim   = quotes . text . show $ elim

> prettyRef :: Entries -> Name -> Root -> REF -> Doc
> prettyRef aus me root ref@(_ := k :<: ty) = text (christenREF aus me ref) <+> prettyRKind k 
>   <+> pretty (christen aus me (bquote B0 ty root))
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> pretty (christen aus me (bquote B0 v root)) 
>               <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyScope :: Scope p String -> Doc
> prettyScope (x :. t)   = 
>     parens (text x <+> text ":." <+> pretty t)
> prettyScope (H g x t)  = 
>     parens (text "\\" <> text x <> text "->" <+> pretty t)
> prettyScope (K t) = parens (text "\\_ ->" <+> pretty t)

> prettyTip :: Entries -> Name -> Tip -> Doc
> prettyTip aus me Module                     = empty
> prettyTip aus me (Unknown     (tv :=>: _))  = text "? :" <+> pretty (christen aus me tv)
> prettyTip aus me (Defined tm  (tv :=>: _))  = pretty (christen aus me tm) 
>     <+> text ":" <+> pretty (christen aus me tv)

> pretty :: Tm {d, p} String -> Doc
> pretty (L s)          = prettyScope s
> pretty (C c)          = prettyCan c
> pretty (N n)          = pretty n
> pretty (Q x)          = text ("?" ++ x)
> pretty (P x)          = text x
> pretty (V i)          = char 'V' <> int i
> pretty (op :@ vs)     = parens (text (opName op) 
>     <+> sep (punctuate comma (map (pretty) vs)))
> pretty (n :$ el)      = parens (pretty n <+> prettyElim el)
> pretty (t :? y)       = parens (pretty t <+> text ":" <+> pretty y)

> import <- Pretty




For debugging purpose, the following quick'n'dirty pretty-printers
might be handy:

> prettyINTM :: INTM -> String
> prettyINTM = show . pretty . christenAbs
>
> prettyVAL :: VAL -> String
> prettyVAL v = show $ pretty $ christenAbs $ bquote B0 v ((B0 :< ("prettyVAL",1),0) :: Root)
>
> prettyREF :: REF -> String
> prettyREF (name := _) = showName name
