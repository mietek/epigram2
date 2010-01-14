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


> renderHouseStyle :: Doc -> String
> renderHouseStyle = render

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
>   <+> pretty (christen aus me (unelaborate (bquote B0 ty root))) ArgSize
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> pretty (christen aus me (unelaborate (bquote B0 v root))) ArgSize
>               <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyTip :: Entries -> Name -> Tip -> Doc
> prettyTip aus me Module                     = empty
> prettyTip aus me (Unknown     (tv :=>: _))  = text "? :" <+> pretty (christen aus me (unelaborate tv)) ArgSize
> prettyTip aus me (Defined tm  (tv :=>: _))  = pretty (christen aus me (unelaborate tm)) ArgSize
>     <+> text ":" <+> pretty (christen aus me (unelaborate tv)) ArgSize


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

> instance Pretty (Can (InDTm String)) where
>     pretty Set       = const (text "Set")
>     pretty (Pi s t)  = prettyPi empty (DPI s t)
>     pretty (Con x)   = wrapDoc (text "con" <+> pretty x ArgSize) AppSize
>     import <- CanPretty
>     pretty can       = const (quotes . text . show $ can)

The |prettyPi| function takes a document representing the domains
so far, a term and the current size. It accumulates domains until a
non(dependent) $\Pi$-type is found, then calls |prettyPiMore| to
produce the final document.

> prettyPi :: Doc -> InDTm String -> Size -> Doc
> prettyPi bs (DPI s (DL (DK t))) = prettyPiMore bs
>     (pretty s (pred PiSize) <+> text "->" <+> pretty t PiSize)
> prettyPi bs (DPI s (DL (x ::. t))) =
>     prettyPi (bs <> parens (text x <+> text ":" <+> pretty s maxBound)) t
> prettyPi bs (DPI s (DN t))  =
>     prettyPi bs (DPI s (DL ("__x" ::. DN (t ::$ A (DN (DP "__x"))))))
> prettyPi bs (DPI s t) = prettyPiMore bs
>     (parens (text "BadPi" <+> pretty s minBound <+> pretty t minBound))
> prettyPi bs tm = prettyPiMore bs (pretty tm PiSize)

The |prettyPiMore| function takes a bunch of domains (which may be empty)
and a codomain, and represents them appropriately for the current size.

> prettyPiMore :: Doc -> Doc -> Size -> Doc
> prettyPiMore bs d
>   | isEmpty bs = wrapDoc d PiSize
>   | otherwise = wrapDoc (bs <+> text "->" <+> d) PiSize


The |Elim| functor is straightforward.

> instance Pretty (Elim (InDTm String)) where
>     pretty (A t)  = pretty t
>     pretty Out    = const (text "%")
>     import <- ElimPretty
>     pretty elim   = const (quotes . text . show $ elim)


To pretty-print a scope, we accumulate arguments until something other
than a $\lamda$-term is reached.

> instance Pretty (DScope String) where
>     pretty s = prettyLambda (B0 :< dScopeName s) (dScopeTm s)

> prettyLambda :: Bwd String -> InDTm String -> Size -> Doc
> prettyLambda vs (DL s) = prettyLambda (vs :< dScopeName s) (dScopeTm s)
> prettyLambda vs tm = wrapDoc
>     (text "\\" <+> text (intercalate " " (trail vs)) <+> text "->"
>         <+> pretty tm ArrSize)
>     minBound


> instance Pretty (InDTm String) where
>     pretty (DL s)          = pretty s
>     pretty (DC c)          = pretty c
>     pretty (DN n)          = pretty n
>     pretty (DQ x)          = const (text ("?" ++ x))
>     import <- InDTmPretty
>     pretty indtm           = const (quotes . text . show $ indtm)


> instance Pretty (ExDTm String) where
>     pretty (DP x)       = const (text x)
>     pretty (DV i)       = const (text "BadV" <> int i)
>     pretty (op ::@ vs)  = wrapDoc
>         (text (opName op) <+> parens
>             (fsep (punctuate comma (map (flip pretty ArgSize) vs))))
>         ArgSize
>     pretty (n ::$ el)   = (\curSize -> wrapDoc
>         (pretty n curSize <+> pretty el ArgSize)
>         AppSize curSize)
>     pretty (t ::? y)    = wrapDoc
>         (pretty t AscSize <+> text ":" <+> pretty y AscSize)
>         AscSize
>     import <- ExDTmPretty
>     pretty exdtm        = const (quotes . text . show $ exdtm)


> import <- Pretty


For debugging purpose, the following quick'n'dirty pretty-printers
might be handy:

> prettyINTM :: INTM -> String
> prettyINTM = renderHouseStyle . flip pretty maxBound . unelaborate . christenAbs
>
> prettyVAL :: VAL -> String
> prettyVAL v = renderHouseStyle $ flip pretty maxBound $ unelaborate $ christenAbs $ bquote B0 v ((B0 :< ("prettyVAL",1),0) :: Root)
>
> prettyREF :: REF -> String
> prettyREF (name := _) = showName name
