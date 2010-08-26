\section{Pretty-printing}
\label{sec:DisplayLang.PrettyPrint}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
>     TypeSynonymInstances #-}

> module DisplayLang.PrettyPrint where

> import Data.List
> import Text.PrettyPrint.HughesPJ

> import ProofState.Structure.Developments

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer

> import Features.Features ()

> import Evidences.Tm

> import Kit.BwdFwd
> import Kit.MissingLibrary hiding ((<+>))

%endif

We use the |HughesPJ| pretty-printing combinators. This section defines how
to pretty-print everything defined in the Core chapter, and provides she
aspects to allow features to add their own pretty-printing support.

The |kword| function gives the document representing a |Keyword|.

> kword :: Keyword -> Doc
> kword = text . key

The |Pretty| class describes things that can be pretty-printed. The
|pretty| function takes a value |x| and the |Size| at which it should be
printed, and should return a document representation of |x|. 

> class Show x => Pretty x where
>     pretty :: x -> Size -> Doc

The |wrapDoc| operator takes a document, its size and the size it should
be printed at. If the document's size is larger than the current size,
it is wrapped in parentheses. 

> wrapDoc :: Doc -> Size -> Size -> Doc
> wrapDoc d dSize curSize
>   | dSize > curSize  = parens d
>   | otherwise        = d

When defining instances of |Pretty|, we will typically pattern-match on
the first argument and construct a function that takes the current size
by partially applying |wrapDoc| to a document and its size.


The |Can| functor is fairly easy to pretty-print, the only complexity
being with $\Pi$-types.

> instance Pretty (Can DInTmRN) where
>     pretty Set       = const (kword KwSet)
>     pretty (Pi s t)  = prettyPi empty (DPI s t)
>     pretty (Con x)   = wrapDoc (kword KwCon <+> pretty x ArgSize) AppSize
>     import <- CanPretty
>     pretty can       = const (quotes . text . show $ can)

The |prettyPi| function takes a document representing the domains
so far, a term and the current size. It accumulates domains until a
non(dependent) $\Pi$-type is found, then calls |prettyPiMore| to
produce the final document.

> prettyPi :: Doc -> DInTmRN -> Size -> Doc
> prettyPi bs (DPI s (DL (DK t))) = prettyPiMore bs
>     (pretty s (pred PiSize) <+> kword KwArr <+> pretty t PiSize)
> prettyPi bs (DPI s (DL (x ::. t))) =
>     prettyPi (bs <> parens (text x <+> kword KwAsc <+> pretty s maxBound)) t
> prettyPi bs (DPI s t) = prettyPiMore bs
>     (kword KwPi <+> pretty s minBound <+> pretty t minBound)
> prettyPi bs tm = prettyPiMore bs (pretty tm PiSize)

The |prettyPiMore| function takes a bunch of domains (which may be empty)
and a codomain, and represents them appropriately for the current size.

> prettyPiMore :: Doc -> Doc -> Size -> Doc
> prettyPiMore bs d
>   | isEmpty bs  = wrapDoc d PiSize
>   | otherwise   = wrapDoc (bs <+> kword KwArr <+> d) PiSize


The |Elim| functor is straightforward.

> instance Pretty (Elim DInTmRN) where
>     pretty (A t)  = pretty t
>     pretty Out    = const (kword KwOut)
>     import <- ElimPretty
>     pretty elim   = const (quotes . text . show $ elim)


To pretty-print a scope, we accumulate arguments until something other
than a $\lambda$-term is reached.

> instance Pretty DSCOPE where
>     pretty s = prettyLambda (B0 :< dScopeName s) (dScopeTm s)

> prettyLambda :: Bwd String -> DInTmRN -> Size -> Doc
> prettyLambda vs (DL s) = prettyLambda (vs :< dScopeName s) (dScopeTm s)
> prettyLambda vs tm = wrapDoc
>     (kword KwLambda <+> text (intercalate " " (trail vs)) <+> kword KwArr
>         <+> pretty tm ArrSize)
>     ArrSize


> instance Pretty DInTmRN where
>     pretty (DL s)          = pretty s
>     pretty (DC c)          = pretty c
>     pretty (DN n)          = pretty n
>     pretty (DQ x)          = const (char '?' <> text x)
>     pretty DU              = const (kword KwUnderscore)
>     import <- DInTmPretty
>     pretty indtm           = const (quotes . text . show $ indtm)


> instance Pretty DExTmRN where
>     pretty (n ::$ [])   = pretty n
>     pretty (n ::$ els)  = wrapDoc
>         (pretty n AppSize <+> hsep (map (flip pretty ArgSize) els))
>         AppSize

> instance Pretty DHEAD where
>     pretty (DP x)       = const (text (showRelName x)) 
>     pretty (DType ty)   = const (parens (kword KwAsc <+> pretty ty maxBound))
>     pretty (DTEx ex)    = const (quotes . text . show $ ex)

> instance Pretty (Scheme DInTmRN) where
>     pretty (SchType ty) = wrapDoc (kword KwAsc <+> pretty ty maxBound) ArrSize
>     pretty (SchExplicitPi (x :<: schS) schT) = wrapDoc (
>         parens (text x <+> pretty schS maxBound)
>             <+> pretty schT maxBound
>         ) ArrSize
>     pretty (SchImplicitPi (x :<: s) schT) = wrapDoc (
>         braces (text x <+> kword KwAsc <+> pretty s maxBound)
>             <+> pretty schT maxBound
>         ) ArrSize         

> import <- Pretty


The |prettyBKind| function pretty-prints a |ParamKind| if supplied
with a document representing its name and type.

> prettyBKind :: ParamKind -> Doc -> Doc
> prettyBKind ParamLam  d = kword KwLambda <+> d <+> kword KwArr
> prettyBKind ParamAll  d = kword KwLambda <+> d <+> kword KwImp
> prettyBKind ParamPi   d = parens d <+> kword KwArr

The |renderHouseStyle| hook allows us to customise the document rendering
if necessary.

> renderHouseStyle :: Doc -> String
> renderHouseStyle = render
