\section{Pretty-printing}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module PrettyPrint (pretty, prettyDev, prettyRef, printDev) where

> import Data.Foldable
> import Data.List
> import Data.Monoid (Monoid, mempty, mappend)
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

The following uses the |HughesPJ| pretty-printing combinators.

> prettyCan :: Can (Tm {d, p} String) -> Doc
> prettyCan Set       = text "*"
> prettyCan (Pi s (L (K t)))  = parens (sep [pretty s <+> text "->", pretty t])
> prettyCan (Pi s (L (H B0 x t)))  = 
>     parens (sep [parens (text x <+> text ":" <+> pretty s) <+> text "->", pretty t])
> prettyCan (Pi s (L (x :. t))) = 
>     parens (sep [parens (text x <+> text ":" <+> pretty s) <+> text "->", pretty t])
> prettyCan (Pi s t)  = text "Pi" <+> (parens (pretty s) $$ parens (pretty t))
> prettyCan (Con x)   = pretty x
> import <- CanPretty
> prettyCan can       = quotes . text .show $ can


> instance Monoid Doc where
>     mempty = empty
>     mappend = ($+$)

> prettyDev :: Bwd Entry -> Name -> Dev -> Doc
> prettyDev aus me (B0, t, _) = brackets empty <+> prettyTip aus me t
> prettyDev aus me (es, t, r) = lbrack <+> foldMap prettyEntry es $$ rbrack 
>     <+> prettyTip aus me t
>   where
>     prettyEntry :: Entry -> Doc
>     prettyEntry (E ref _ (Boy k) _) = prettyBKind k <+> prettyRef aus me r ref
>     prettyEntry (E ref _ (Girl LETG d) _) = sep [prettyRef aus me r ref, 
>                                                      nest 4 (prettyDev aus me d)]
>
>     prettyBKind :: BoyKind -> Doc
>     prettyBKind LAMB  = text "\\"
>     prettyBKind PIB   = text "Pi"


> prettyElim :: Elim (Tm {d, p} String) -> Doc
> prettyElim (A t)  = pretty t
> prettyElim Out    = text "Out"
> import <- ElimPretty
> prettyElim elim   = quotes . text . show $ elim

> prettyRef :: Bwd Entry -> Name -> Root -> REF -> Doc
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
>     parens (text "\\" <> text x <> text "." <+> pretty t)
> prettyScope (K t) = parens (text "\\_." <+> pretty t)

> prettyTip :: Bwd Entry -> Name -> Tip -> Doc
> prettyTip aus me Module                     = empty
> prettyTip aus me (Unknown     (tv :=>: _))  = text ":= ? :" <+> pretty (christen aus me tv)
> prettyTip aus me (Defined tm  (tv :=>: _))  = text ":=" <+> pretty (christen aus me tm) 
>     <+> text ":" <+> pretty (christen aus me tv)

> pretty :: Tm {d, p} String -> Doc
> pretty (L s)          = prettyScope s
> pretty (C c)          = prettyCan c
> pretty (N n)          = pretty n
> pretty (P x)          = text x
> pretty (V i)          = char 'V' <> int i
> pretty (op :@ vs)     = parens (text (opName op) 
>     <+> sep (punctuate comma (map (pretty) vs)))
> pretty (n :$ el)      = parens (pretty n <+> prettyElim el)
> pretty (t :? y)       = parens (pretty t <+> text ":" <+> pretty y)

> printDev :: Bwd Entry -> Name -> Dev -> IO ()
> printDev aus n d = putStrLn . show $ prettyDev aus n d


> import <- Pretty



