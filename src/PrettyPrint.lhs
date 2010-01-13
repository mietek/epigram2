\section{Pretty-printing}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances #-}

> module PrettyPrint where

> import MissingLibrary
> import Data.Foldable
> import Data.List
> import Text.PrettyPrint.HughesPJ

> import BwdFwd hiding ((<+>))
> import qualified BwdFwd ((<+>))
> import Developments
> import DisplayTm
> import Features
> import Naming
> import Root
> import Rules hiding (($$))
> import Tm

%endif

The following uses the |HughesPJ| pretty-printing combinators. We define how to
pretty-print everything defined in the Core chapter here, and provide she aspects
to allow extra canonical terms and eliminators to be pretty-printed.


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

If enabled, this case will print the fully lifted definition and type
(as contained in the reference) for each girl, which may be helpful
for debugging.

<     prettyEntries (es' :< E ref _ (Girl LETG dev) _) (aus' :< _) = 
<         prettyEntries es' aus'
<         $$ sep [prettyRef aus me r ref,
<                 nest 2 (prettyDev aus' (refName ref) dev) <+> semi]
                                         
>     prettyEntries (es' :< e) (aus' :< _) = 
>         prettyEntries es' aus'
>         $$ sep [text (christenName aus me (entryName e)),
>                 nest 2 (prettyDev aus' (entryName e) (entryDev e)) <+> semi]
>
>     prettyEntries B0 _ = empty
>
> prettyBKind :: BoyKind -> Doc -> Doc
> prettyBKind LAMB  d = text "\\" <+> d <+> text "->"
> prettyBKind ALAB  d = text "\\" <+> d <+> text "=>"
> prettyBKind PIB   d = parens d <+> text "->"

> prettyRef :: Entries -> Name -> Root -> REF -> Doc
> prettyRef aus me root ref@(_ := k :<: ty) = text (christenREF aus me ref) <+> prettyRKind k 
>   <+> pretty (christen aus me (unelaborate (bquote B0 ty root)))
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> pretty (christen aus me (unelaborate (bquote B0 v root)))
>               <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyDScope :: Pretty x => DScope x -> Doc
> prettyDScope (x ::. t)  = parens (text x <+> text "::." <+> pretty t)
> prettyDScope (DK t)     = parens (text "\\_ ->" <+> pretty t)

> prettyTip :: Entries -> Name -> Tip -> Doc
> prettyTip aus me Module                     = empty
> prettyTip aus me (Unknown     (tv :=>: _))  = text "? :" <+> pretty (christen aus me (unelaborate tv))
> prettyTip aus me (Defined tm  (tv :=>: _))  = pretty (christen aus me (unelaborate tm))
>     <+> text ":" <+> pretty (christen aus me (unelaborate tv))



> class Show x => Pretty x where
>     pretty :: x -> Doc

> instance Pretty [Char] where
>     pretty = text

> instance Pretty x => Pretty (Can (InDTm x)) where
>     pretty Set       = text "*"
>     pretty (Pi s (DL (DK t)))  = parens (sep [pretty s <+> text "->", pretty t])
>     pretty (Pi s (DL (x ::. t))) = 
>         parens (sep [parens (text x <+> text ":" <+> pretty s) <+> text "->", pretty t])
>     pretty (Pi s t)  = parens (text "Pi" <+> pretty s <+> pretty t)
>     pretty (Con x)   = text "@" <+> pretty x
>     import <- CanPretty
>     pretty can       = quotes . text . show $ can

> instance Pretty x => Pretty (Elim (InDTm x)) where
>     pretty (A t)  = pretty t
>     pretty Out    = text "Out"
>     import <- ElimPretty
>     pretty elim   = quotes . text . show $ elim

> instance Pretty x => Pretty (InDTm x) where
>     pretty (DL s)          = prettyDScope s
>     pretty (DC c)          = pretty c
>     pretty (DN n)          = pretty n
>     pretty (DQ x)          = text ("?" ++ x)

> instance Pretty x => Pretty (ExDTm x) where
>     pretty (DP x)          = pretty x
>     pretty (DV i)          = char 'V' <> int i
>     pretty (op ::@ vs)     = parens (text (opName op) 
>         <+> sep (punctuate comma (map (pretty) vs)))
>     pretty (n ::$ el)      = parens (pretty n <+> pretty el)
>     pretty (t ::? y)       = parens (pretty t <+> text ":" <+> pretty y)

> import <- Pretty


For debugging purpose, the following quick'n'dirty pretty-printers
might be handy:

> prettyINTM :: INTM -> String
> prettyINTM = show . pretty . unelaborate . christenAbs
>
> prettyVAL :: VAL -> String
> prettyVAL v = show $ pretty $ unelaborate $ christenAbs $ bquote B0 v ((B0 :< ("prettyVAL",1),0) :: Root)
>
> prettyREF :: REF -> String
> prettyREF (name := _) = showName name
