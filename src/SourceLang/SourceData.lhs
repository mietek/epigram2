\section{SourceData}
\label{sec:SourceLang.SourceData}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TypeOperators,
>     GADTs, RankNTypes, KindSignatures, TypeFamilies, MultiParamTypeClasses #-}

> module SourceLang.SourceData where

> import ShePrelude
> import Data.Foldable
> import Data.Traversable

> import SourceLang.Lexer
> import SourceLang.Parx

%endif

> type Template = String -- this will change
> type Arg = Template -- really?

A document is a sequence of definitions.

> type EpiDoc = [Nest :~ EpiDef]

A definition is a declaration (keyword with signature) and a dialogue.
There are three varieties.

> data DefKind :: * where
>   DataDef    :: DefKind
>   LetDef     :: DefKind
>   LemmaDef   :: DefKind
>   VarDef     :: DefKind
>   deriving (Show, Eq, SheSingleton)

> data Some :: * -> * where
>   Some :: forall t. pi (x :: t). Some t

> data EpiDef :: * where
>   Def :: pi (k :: DefKind).
>          Nest :~ EpiSig {k} -> Nest :~ (EpiDial {k}) -> EpiDef

> instance Show EpiDef where
>   show (Def {DataDef}   s d) = "data " ++ show s ++ " where " ++ show d
>   show (Def {LetDef}    s d) = "let " ++ show s ++ " where " ++ show d
>   show (Def {LemmaDef}  s d) = "lemma " ++ show s ++ " where " ++ show d

> data EpiSig :: {DefKind} -> * where
>   Sig :: [Nest :~ EpiPrem] -> Elt :~ (EpiConc {k}) -> EpiSig {k}

> instance Show (EpiSig k) where
>   show (Sig ps c) = show ps ++ " --- " ++ show c

> data EpiPrem :: * where
>   VarPrem :: EpiSig {VarDef} -> EpiPrem
>   PrfPrem :: EpiSig {LemmaDef} -> EpiPrem

> instance Show EpiPrem where
>   show (VarPrem s) = "(" ++ show s ++ ")"
>   show (PrfPrem s) = "(" ++ show s ++ ")"

> data EpiConc :: {DefKind} -> * where
>   DataConc :: Elt :~ Template -> [Elt :~ Arg] ->
>               EpiConc {DataDef} -- just Arg?
>   LetConc :: Elt :~ Template -> [Elt :~ Arg] -> 
>              Elt :~ EpiInTm -> EpiConc {LetDef}
>   VarConc :: Elt :~ Template -> [Elt :~ Arg] -> 
>              Maybe (Elt :~ EpiInTm) -> EpiConc {VarDef}
>   LemmaConc :: Elt :~ EpiInTm -> EpiConc {LemmaDef}

> instance Show (EpiConc {k}) where
>   show (DataConc f as) = show f ++ show as ++ " : Set"
>   show (LetConc f as t) = show f ++ show as ++ " : " ++ show t
>   show (VarConc f as Nothing) = show f ++ show as
>   show (VarConc f as (Just t)) = show f ++ show as ++ " : " ++ show t
>   show (LemmaConc p) = ":- " ++ show p

> data EpiDial :: {DefKind} -> * where
>   Dial :: Elt :~ (EpiProb {k}) -> [Nest :~ (EpiStrat {k})] ->
>           [Nest :~ (EpiDial {k})] -> EpiDoc -> EpiDial {k}
>   NilDial :: EpiDial {DataDef}
>   ConsDial :: Elt :~ (EpiProb {DataDef}) ->
>               [(Elt :~ Template, [Nest :~ (EpiSig {VarDef})])] ->
>               Nest :~ EpiDial {DataDef} -> EpiDial {DataDef}
>   DotDotDot :: EpiDial {k}

> denture :: String -> String
> denture = unlines . map ("  " ++) . lines

> instance Show (EpiDial k) where
>   show (Dial p ss ds ws) =
>     show p ++ " " ++ show ss ++ "\n"
>       ++ denture (ds >>= show) ++
>       if null ws then "" else "  where\n" ++ denture (ws >>= show)
>   show NilDial = ""
>   show (ConsDial p css d) =
>     show p ++ " :> " ++ foldMap cof css ++ "\n" ++ show d where
>       cof (c, ss) = ":> " ++ show c ++ foldMap bof ss ++ "\n"
>       bof a = "(" ++ show a ++ ")"
>   show DotDotDot = "..."

> data EpiProb :: {DefKind} -> * where
>   ProgProb :: Elt :~ Template -> [Elt :~ EpiInTm] -> [Elt :~ EpiInTm] ->
>             EpiProb {LetDef}
>   ProofProb :: Elt :~ (EpiSig {LemmaDef}) ->  [Elt :~ EpiInTm] ->
>             EpiProb {LemmaDef}
>   DataProb :: Elt :~ Template -> [Elt :~ EpiInTm] -> [Elt :~ EpiInTm] ->
>             EpiProb {DataDef}

> instance Show (EpiProb k) where
>   show (ProgProb f as ws) = show f ++ show as ++
>     if null ws then "" else " | " ++ show ws
>   show (ProofProb s ws) = show s ++
>     if null ws then "" else " | " ++ show ws
>   show (DataProb f as ws) = show f ++ show as ++
>     if null ws then "" else " | " ++ show ws

> data EpiStrat :: {DefKind} -> * where
>   EBy :: Elt :~ EpiExTm -> EpiStrat {k}
>   EWith :: Elt :~ EpiExTm -> EpiStrat {k}
>   ERet :: Elt :~ EpiInTm -> EpiStrat {LetDef}
>   EBecause :: Elt :~ EpiInTm -> [Elt :~ EpiInTm] ->
>               EpiStrat {LemmaDef}

> instance Show (EpiStrat k) where
>   show (EBy gum) = " <= " ++ show gum
>   show (EWith w) = " with " ++ show w
>   show (ERet t) = " = " ++ show t
>   show (EBecause p as) = " -: " ++ show p ++ " for " ++ show as

> data EpiInTm :: * where
>   EEx :: EpiExTm -> EpiInTm
>   ESet :: EpiInTm
>   EPi, ESig, ELam
>     :: Elt :~ (EpiSig {VarDef}) -> Elt :~ EpiInTm -> EpiInTm
>   EV :: EpiInTm
>   EP :: Elt :~ EpiInTm -> Elt :~ EpiInTm -> EpiInTm
>   EC :: Elt :~ Template -> [Elt :~ EpiInTm] -> EpiInTm
>   EShed :: EpiInTm
>   deriving Show

> data EpiExTm :: * where
>   EVS :: Elt :~ Template -> [Elt :~ EpiElim] -> EpiExTm
>   deriving Show

> data EpiElim :: * where
>   EA :: EpiInTm -> EpiElim
>   EJ :: Int -> EpiElim
>   deriving Show

> exampleEpiDoc :: EpiDoc
> exampleEpiDoc =
>   [  [] :~ Def {DataDef}
>        ([] :~ Sig [] ([] :~ DataConc ([] :~ "Nat") []))
>        ([] :~ ConsDial ([] :~ DataProb ([] :~ "Nat") [] [])
>          [([] :~ "zero", []),
>           ([] :~ "suc",
>            [[] :~ Sig []
>               ([] :~ VarConc ([] :~ "n") []
>                 (Just ([] :~ EEx (EVS ([] :~ "Nat") []))))])]
>             ([] :~ NilDial))
>   ]
