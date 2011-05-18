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
> -- import DisplayLang.Scheme
> import DisplayLang.Lexer

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

> instance Pretty Can where
>   pretty Set    = const (kword KwSet)
>   pretty Con    = const (kword KwCon)
>   pretty Zero   = const (kword KwAbsurd)
>   pretty One    = const (kword KwTrivial)
>   pretty Prf    = const (kword KwPrf)
>   pretty Prop   = const (kword KwProp)
>   pretty Inh    = const (kword KwInh)
>   pretty Wit    = const (kword KwWit)
>   -- [Feature = Enum]
>   pretty EnumU  = const (kword KwEnumU)
>   pretty EnumT  = const (kword KwEnum) 
>   -- [/Feature = Enum]
>     -- [Feature = UId]
>   pretty UId      = const (kword KwUId)
>   pretty (Tag s)  = const (kword KwTag <> text s)
>   -- [/Feature = UId]
>   pretty c        = error $ show c

> {-
> instance Pretty (Can DInTmRN) where
>     pretty Set       = const (kword KwSet)
>     pretty (Pi s t)  = prettyPi empty (DPI s t)
>     pretty (Con x)   = wrapDoc (kword KwCon <+> pretty x ArgSize) AppSize
>     -- import <- CanPretty
>     -- [Feature = Anchor]
>     pretty (Anchor (DTAG u) t ts) = wrapDoc (text u <+> pretty ts ArgSize) ArgSize
>     pretty AllowedEpsilon = const empty
>     pretty (AllowedCons _ _ _ s ts) = wrapDoc (pretty s ArgSize <+> pretty ts ArgSize) ArgSize
>     {- Not yet implemented -}
>     -- [/Feature = Anchor]
>     -- [Feature = Enum]
>     pretty (EnumT t)  = wrapDoc (kword KwEnum <+> pretty t ArgSize) AppSize
>     pretty Ze         = const (int 0)
>     pretty (Su t)     = prettyEnumIndex 1 t
>     -- [/Feature = Enum]
>     -- [Feature = Equality]
>     pretty (EqBlue pp qq) = pretty (DEqBlue (foo pp) (foo qq))
>       where
>         foo :: (DInTmRN :>: DInTmRN) -> DExTmRN
>         foo (_    :>: DN x  ) = x
>         foo (xty  :>: x     ) = DType xty ::$ [A x] 
>     -- [/Feature = Equality]
>     -- [Feature = IDesc]
>     pretty (IMu (Just l   :?=: _) i)  = wrapDoc
>         (pretty l AppSize <+> pretty i ArgSize)
>         AppSize
>     pretty (IMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
>         (kword KwIMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
>         AppSize
>     -- [/Feature = IDesc]
>     -- [Feature = Labelled]
>     pretty (Label l t) = const (kword KwLabel <+>
>         pretty l maxBound <+> kword KwAsc <+> pretty t maxBound
>         <+> kword KwLabelEnd)
>     pretty (LRet x) = wrapDoc (kword KwRet <+> pretty x ArgSize) ArgSize
>     -- [/Feature = Labelled]
>     -- [Feature = Prop]
>     pretty Prop           = const (kword KwProp)
>     pretty (Prf p)        = wrapDoc (kword KwPrf <+> pretty p AndSize) AppSize
>     pretty (All p q)      = prettyAll empty (DALL p q)
>     pretty (And p q)      = wrapDoc
>         (pretty p (pred AndSize) <+> kword KwAnd <+> pretty q AndSize)
>         AndSize
>     pretty Trivial        = const (kword KwTrivial)
>     pretty Absurd         = const (kword KwAbsurd)
>     pretty (Box (Irr p))  = pretty p
>     pretty (Inh ty)       = wrapDoc (kword KwInh <+> pretty ty ArgSize) AppSize
>     pretty (Wit t)        = wrapDoc (kword KwWit <+> pretty t ArgSize) AppSize
>     -- [/Feature = Prop]
>     -- [Feature = Sigma]
>     pretty Unit         = wrapDoc (kword KwSig <+> parens empty) AppSize
>     pretty Void         = prettyPair DVOID
>     pretty (Sigma s t)  = prettySigma empty (DSIGMA s t)
>     pretty (Pair a b)   = prettyPair (DPAIR a b)
>     -- [/Feature = Sigma]
>
> -}



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
>     -- import <- ElimPretty
>     -- [Feature = Labelled]
>     -- pretty (Call _) = const (kword KwCall)
>     -- [/Feature = Labelled]
>     -- [Feature = Sigma]
>     pretty Hd = const (kword KwFst)
>     pretty Tl = const (kword KwSnd)
>     -- [/Feature = Sigma]
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
>     pretty (DL s)                   = pretty s
>     pretty (DC Pi [s , t])          = prettyPi empty (DPI s t)
>     pretty (DC One [])              = wrapDoc (kword KwSig <+> parens empty) AppSize
>     pretty (DC Zero [])             = prettyPair DVOID
>     pretty (DC Sigma [s , t])       = prettySigma empty (DSIGMA s t)
>     pretty (DC Pair [a , b])        = prettyPair (DPAIR a b)
>     -- [Feature = Prop]
>     pretty (DC And [p, q])      = wrapDoc
>         (pretty p (pred AndSize) <+> kword KwAnd <+> pretty q AndSize)
>         AndSize
>     pretty (DC Prf [DALL p q])  = 
>       wrapDoc (pretty Prf AppSize <+> prettyAll empty (DALL p q) ArgSize) AppSize
>     -- [/Feature = Prop]
>     -- [Feature = Enum]
>     pretty (DC Ze [])           = const (int 0)
>     pretty (DC Su [])          = error "NYERK" -- prettyEnumIndex 1 t
>     pretty (DC Su [t])          = prettyEnumIndex 1 t
>     pretty (DC NilE [])              = prettyEnumU DNILE
>     pretty (DC ConsE [a , b])        = prettyEnumU (DCONSE a b)
>     -- [/Feature = Enum]
>     pretty (DC c [])       = pretty c
>     pretty (DC c as)  = wrapDoc
>         (pretty c AppSize <+> hsep (map (flip pretty ArgSize) as))
>         AppSize
>     pretty (DN n)          = pretty n
>     pretty (DQ x)          = const (char '?' <> text x)
>     pretty DU              = const (kword KwUnderscore)

<     -- import <- DInTmPretty
<     {-- [Feature = Anchor]
<     pretty (DANCHOR s args)  = wrapDoc (text s <+> pretty args ArgSize) ArgSize
<     -- [/Feature = Anchor]
<     -- [Feature = Equality]
<     pretty (DEqBlue t u) = wrapDoc
<       (pretty t ArgSize <+> kword KwEqBlue <+> pretty u ArgSize)
<       ArgSize
<     -- [/Feature = Equality]
<     -- [Feature = IDesc]
<     pretty (DIMu (Just s   :?=: _) _)  = pretty s
<     pretty (DIMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
<         (kword KwIMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
<         AppSize
<     -- [/Feature = IDesc]

>     -- [Feature = UId]
>     pretty (DTAG s)     = const (kword KwTag <> text s)
>     pretty (DC (Tag s) xs)  = wrapDoc (kword KwTag <> text s
>       <+> hsep (map (flip pretty ArgSize) xs)) AppSize
>     -- [/Feature = UId]

>     pretty (DTIN indtm)           = const (quotes . text . show $ indtm)


> instance Pretty DExTmRN where
>     pretty (n ::$ [])   = pretty n
>     pretty (n ::$ els)  = wrapDoc
>         (pretty n AppSize <+> hsep (map (flip pretty ArgSize) (trail els)))
>         AppSize

> instance Pretty DHEAD where
>     pretty (DP x)       = const (text (showRelName x)) 
>     pretty (DType ty)   = const (parens (kword KwAsc <+> pretty ty maxBound))
>     pretty (DTEx ex)    = const (quotes . text . show $ ex)

> {-
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
> -}

> -- import <- Pretty
> -- [Feature = UId]
> prettyEnumIndex :: Int -> DInTmRN -> Size -> Doc
> prettyEnumIndex n DZE      = const (int n)
> prettyEnumIndex n (DSU t)  = prettyEnumIndex (succ n) t
> prettyEnumIndex n tm       = wrapDoc
>     (int n <+> kword KwPlus <+> pretty tm ArgSize)
>     AppSize
> -- [/Feature = UId]

> -- [Feature = Prop]
> prettyAll :: Doc -> DInTmRN -> Size -> Doc
> prettyAll bs (DALL (DPRF p) (DL (DK q))) = prettyAllMore bs
>   (pretty p (pred PiSize) <+> kword KwImp <+> pretty q PiSize)
> prettyAll bs (DALL s (DL (x ::. t))) =
>   prettyAll (bs <> parens (text x <+> kword KwAsc <+> pretty s maxBound)) t
> prettyAll bs (DALL s (DL (DK t))) = prettyAll bs (DALL s (DL ("_" ::. t)))
> prettyAll bs (DALL s t) = prettyAllMore bs
>   (kword KwAll <+> pretty s minBound <+> pretty t minBound)
> prettyAll bs tm = prettyAllMore bs (pretty tm PiSize)
>
> prettyAllMore :: Doc -> Doc -> Size -> Doc
> prettyAllMore bs d
>   | isEmpty bs  = wrapDoc d PiSize
>   | otherwise   = wrapDoc (bs <+> kword KwImp <+> d) PiSize
> -- [/Feature = Prop]

> -- [Feature = Sigma]
> prettyPair :: DInTmRN -> Size -> Doc
> prettyPair p = const (brackets (prettyPairMore empty p))

> prettyPairMore :: Doc -> DInTmRN -> Doc
> prettyPairMore d DVOID        = d
> prettyPairMore d (DPAIR a b)  = prettyPairMore (d <+> pretty a minBound) b
> prettyPairMore d t            = d <+> kword KwComma <+> pretty t maxBound

> prettySigma :: Doc -> DInTmRN -> Size -> Doc
> prettySigma d DUNIT                      = prettySigmaDone d empty
> prettySigma d (DSIGMA s (DL (x ::. t)))  = prettySigma
>     (d <+> text x <+> kword KwAsc <+> pretty s maxBound <+> kword KwSemi) t
> prettySigma d (DSIGMA s (DL (DK t)))     = prettySigma
>     (d <+> pretty s maxBound <+> kword KwSemi) t
> prettySigma d (DSIGMA s t) = prettySigmaDone d 
>     (kword KwSig <+> pretty s minBound <+> pretty t minBound)
> prettySigma d t = prettySigmaDone d (pretty t maxBound)

> prettySigmaDone :: Doc -> Doc -> Size -> Doc
> prettySigmaDone s t
>   | isEmpty s  = wrapDoc t AppSize
>   | otherwise  = wrapDoc (kword KwSig <+> parens (s <+> t)) AppSize
> -- [/Feature = Sigma] 

> -- [Feature = Enum]
> prettyEnumU :: DInTmRN -> Size -> Doc
> prettyEnumU p = const (brackets (prettyEnumUMore empty p))

> prettyEnumUMore :: Doc -> DInTmRN -> Doc
> prettyEnumUMore d DNILE        = d
> prettyEnumUMore d (DCONSE a b)  = prettyEnumUMore (d <+> pretty a minBound) b
> prettyEnumUMore d t            = d <+> kword KwComma <+> pretty t maxBound
> -- [/Feature = Enum]

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
