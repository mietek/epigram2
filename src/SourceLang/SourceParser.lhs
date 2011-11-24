> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE PatternGuards, FlexibleInstances, RankNTypes, TypeOperators,
>     TupleSections, GADTs #-}

> module SourceLang.SourceParser where

> import Prelude hiding (elem, all)
> import Control.Applicative
> import Data.Foldable
> import ShePrelude
> import Data.Char

> import SourceLang.Parx
> import SourceLang.Lexer
> import SourceLang.SourceData

> isWhite :: Elt -> Bool
> isWhite (M _) = True
> isWhite (E (Spc _)) = True
> isWhite (E (Sym ";")) = True
> isWhite _ = False

> instance Gappy Elt where
>   gap = (|() (-many (tok isWhite)-)|)

> nest :: Parx Elt x -> (x -> Parx Nest y) -> Parx Nest y
> nest pe pn = like $ \ (es :# ns) -> case parx pe es of
>   (_, Just x, []) -> case parx (pn x) ns of
>     (_, Just y, []) -> (|y|)
>     _ -> (|)
>   _ -> (|)

> brackElt :: BType -> Parx Elt t -> Parx Elt t
> brackElt b p = like br where
>   br (B b' es (Right _)) | b == b' = case parx p es of
>     (_, Just x, []) -> (|x|)
>     _ -> (|)
>   br _ = (|)

> brackNest :: BType -> Parx Nest t -> Parx Elt t
> brackNest b p = like br where
>   br (B b' es (Right _)) | b == b' = case parx p (nestLines es) of
>     (_, Just x, []) -> (|x|)
>     _ -> (|)
>   br _ = (|)

> instance Gappy Nest where
>   gap = (|() (-many (nest gap (|gap|))-)|)

> epiDoc :: Parx Nest EpiDoc
> epiDoc = gmany (source epiDef)

> epunc :: String -> Parx Elt ()
> epunc = punc . E . Sym

> sym :: String -> Parx Elt ()
> sym = teq . E . Sym

> someDefKind :: Parx Elt (Some DefKind)
> someDefKind =
>   (|(Some {DataDef}) (-epunc "data"-)
>    |(Some {LetDef}) (-epunc "let"-)
>    |(Some {LemmaDef}) (-epunc "lemma"-)
>    |)

> epiDef :: Parx Nest EpiDef
> epiDef = nest someDefKind $ \ (Some {k}) ->
>   (|(Def {k}) (source (epiSig {k})) (source (epiDial {k}))|)

> dashing :: Elt -> Bool
> dashing (E (Sym ('-':'-':'-':_))) = True
> dashing _ = False

> rule :: Parx Nest ()
> rule = nest (pad (tok dashing)) (|gap|)

> epiSig :: pi (k :: DefKind). Parx Nest (EpiSig k)
> epiSig {k} =
>   (|mkSig
>     (|id (precook (upto rule) (gmany (source epiPrem)))
>      |[] (-gap-)
>      |)
>     (source (nest (epiConc {k}) $ \ c -> (|c (-gap-)|)))
>    |id (pad (nest (pad (brackNest (Round, Nothing) (epiSig {k})))
>               $ \ c -> (|c (-gap-)|)))
>    |)
>  where mkSig ps (s :~ (qs, c)) = Sig (ps ++ qs) (s :~ c)

> epiPrem :: Parx Nest EpiPrem
> epiPrem =
>   (|VarPrem (epiSig {VarDef})
>    |PrfPrem (epiSig {LemmaDef})
>    |)

> reserved = ["data", "let", "lemma",
>   ":", "<=", "=>", "=", ";", ",", "|", ":>", "*", "\\",
>   "->", "<-", ":-", "-:", "...", ".", "Set", "Prop"]

> numeric :: String -> Bool
> numeric ('-':xs@(_:_)) = all isDigit xs
> numeric xs@(_:_) = all isDigit xs

> number :: Elt -> Maybe Int
> number (E (Sym x)) | numeric x = Just (read x)
> number _ = Nothing

> identifier :: Elt -> Maybe String
> identifier e@(E (Sym x))
>   | not (elem x reserved) && not (numeric x) && not (dashing e) = (|x|)
> identifier _ = (|)

> template :: Parx Elt Template
> template = like identifier

> sigged :: Nest :~ EpiPrem -> [Elt :~ Arg]
> sigged (_ :~ VarPrem (Sig _ (_ :~ VarConc x _ _))) = [x]
> sigged _ = []

> epiArg :: Parx Elt ([Nest :~ EpiPrem], [Elt :~ Arg])
> epiArg =
>   (| ~[], (|source template : ~[]|)
>    |id (brackNest (Round, Nothing) (gmany (source epiPrem)) >>= \ ps ->
>          return (ps, foldMap sigged ps))
>    |)

> epiConc :: pi (k :: DefKind).
>            Parx Elt ([Nest :~ EpiPrem], EpiConc {k})
> epiConc {VarDef} = do
>   gap
>   f <- source template
>   pas <- gmany epiArg
>   mt <- (|Just (-epunc ":"-) (pad (source epiInTm))|Nothing|)
>   gap
>   return (foldMap fst pas, VarConc f (foldMap snd pas) mt)
> epiConc {LetDef} = do
>   gap
>   f <- source template
>   pas <- gmany epiArg
>   t <- (|id (-epunc ":"-) (pad (source epiInTm))|)
>   return (foldMap fst pas, LetConc f (foldMap snd pas) t)
> epiConc {k} = (|)

> epiDial :: pi (k :: DefKind). Parx Nest (EpiDial k)
> epiDial {k} =
>  (|DotDotDot (-nest (gap *> sym "." *> sym "." *> sym "." *> gap) (|gap|)-)|)

Termy things don't consume leading or trailing spaces.

> smallEpiInTm :: Parx Elt EpiInTm
> smallEpiInTm =
>   (|ESet (-sym "Set"-)
>    |EEx (|EVS (source template) ~[]|)
>    |ELam (-sym "\\"-)
>       (pad (source (precook (|(|(upto (sym "->")) :# ~[]|) : ~[]|)
>                     (epiSig {VarDef}))))
>       (source epiInTm)
>    |id (brackElt (Round, Nothing) epiInTm)|)

> epiInTm :: Parx Elt EpiInTm
> epiInTm = source
>   (|EEx epiExTm
>    |(flip ($)) (source (brackNest (Round, Nothing) (epiSig {VarDef})))
>         (|EPi (-epunc "->"-) | ESig (-epunc "*"-)|)
>         (source epiInTm)
>    |id smallEpiInTm|)
>   >>= \ ex@(es :~ x) ->
>   (|id (|EPi (-epunc "->"-) | ESig (-epunc "*"-)|)
>     ~(es :~ Sig [] ([es :# []] :~ VarConc ([] :~ "") [] (Just ex)))
>     (source epiInTm)
>    |x|)

> epiExTm :: Parx Elt EpiExTm
> epiExTm = (|EVS (source template) (many (|id (-gap-) (source epiElim)|))|)

> epiElim :: Parx Elt EpiElim
> epiElim =
>   (|EJ (like number)
>    |EA epiInTm
>    |)
