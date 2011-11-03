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

%endif

> type Source = String -- this will change
> type Template = String -- this will change
> type Arg = Template -- really?

> data Sourced t = Source :~ t deriving (Functor, Foldable, Traversable, Show)

A document is a sequence of definitions.

> type EpiDoc = [Sourced EpiDef]

A definition is a declaration (keyword with signature) and a dialogue.
There are three varieties.

> data DefKind :: * where
>   DataDef    :: DefKind
>   LetDef     :: DefKind
>   LemmaDef   :: DefKind
>   VarDef     :: DefKind
>   deriving (Show, Eq, SheSingleton)

> data EpiDef :: * where
>   Def :: pi (k :: DefKind).
>          Sourced (EpiSig {k}) -> Sourced (EpiDial {k}) -> EpiDef

> instance Show EpiDef where
>   show (Def {DataDef}   s d) = "data " ++ show s ++ " where " ++ show d
>   show (Def {LetDef}    s d) = "data " ++ show s ++ " where " ++ show d
>   show (Def {LemmaDef}  s d) = "data " ++ show s ++ " where " ++ show d

> data EpiSig :: {DefKind} -> * where
>   Sig :: [Sourced EpiPrem] -> Sourced (EpiConc {k}) -> EpiSig {k}

> instance Show (EpiSig k) where
>   show (Sig ps c) = show ps ++ " --- " ++ show c

> data EpiPrem :: * where
>   VarPrem :: EpiSig {VarDef} -> EpiPrem
>   PrfPrem :: EpiSig {LemmaDef} -> EpiPrem

> instance Show EpiPrem where
>   show (VarPrem s) = "(" ++ show s ++ ")"
>   show (PrfPrem s) = "(" ++ show s ++ ")"

> data EpiConc :: {DefKind} -> * where
>   DataConc :: Sourced Template -> [Sourced Arg] ->
>               EpiConc {DataDef} -- just Arg?
>   LetConc :: Sourced Template -> [Sourced Arg] -> 
>              Sourced EpiInTm -> EpiConc {LetDef}
>   VarConc :: Sourced Template -> [Sourced Arg] -> 
>              Maybe (Sourced EpiInTm) -> EpiConc {VarDef}
>   LemmaConc :: Sourced EpiInTm -> EpiConc {LemmaDef}

> instance Show (EpiConc {k}) where
>   show (DataConc f as) = show f ++ show as ++ " : Set"
>   show (LetConc f as t) = show f ++ show as ++ " : " ++ show t
>   show (VarConc f as Nothing) = show f ++ show as
>   show (VarConc f as (Just t)) = show f ++ show as ++ " : " ++ show t
>   show (LemmaConc p) = ":- " ++ show p

> data EpiDial :: {DefKind} -> * where
>   Dial :: Sourced (EpiProb {k}) -> [Sourced (EpiStrat {k})] ->
>           [Sourced (EpiDial {k})] -> EpiDoc -> EpiDial {k}
>   DotDotDot :: EpiDial {k}

> denture :: String -> String
> denture = unlines . map ("  " ++) . lines

> instance Show (EpiDial k) where
>   show (Dial p ss ds ws) =
>     show p ++ " " ++ show ss ++ "\n"
>       ++ denture (ds >>= show) ++
>       if null ws then "" else "  where\n" ++ denture (ws >>= show)
>   show DotDotDot = "..."

> data EpiProb :: {DefKind} -> * where
>   ProgProb :: Sourced Template -> [Sourced EpiInTm] -> [Sourced EpiInTm] ->
>             EpiProb {LetDef}
>   ProofProb :: Sourced (EpiSig {LemmaDef}) ->  [Sourced EpiInTm] ->
>             EpiProb {LemmaDef}
>   DataProb :: Sourced Template -> [Sourced EpiInTm] -> [Sourced EpiInTm] ->
>             EpiProb {DataDef}

> instance Show (EpiProb k) where
>   show (ProgProb f as ws) = show f ++ show as ++
>     if null ws then "" else " | " ++ show ws
>   show (ProofProb s ws) = show s ++
>     if null ws then "" else " | " ++ show ws
>   show (DataProb f as ws) = show f ++ show as ++
>     if null ws then "" else " | " ++ show ws

> data EpiStrat :: {DefKind} -> * where
>   EBy :: Sourced EpiInTm -> EpiStrat {k}
>   EWith :: Sourced EpiExTm -> EpiStrat {k}
>   ERet :: Sourced EpiInTm -> EpiStrat {LetDef}
>   ECons :: Sourced Template -> [Sourced (EpiSig {VarDef})] ->
>            EpiStrat {DataDef}
>   EBecause :: Sourced EpiInTm -> [Sourced EpiInTm] ->
>               EpiStrat {LemmaDef}

> instance Show (EpiStrat k) where
>   show (EBy gum) = " <= " ++ show gum
>   show (EWith w) = " with " ++ show w
>   show (ERet t) = " = " ++ show t
>   show (ECons c ss) = " :> " ++ show c ++ show ss
>   show (EBecause p as) = " -: " ++ show p ++ " for " ++ show as

> data EpiInTm :: * where
>   EEx :: EpiExTm -> EpiInTm
>   ESet :: EpiInTm
>   EPi, ESig, ELam
>     :: Sourced (EpiSig {VarDef}) -> Sourced EpiInTm -> EpiInTm
>   EV :: EpiInTm
>   EP :: Sourced EpiInTm -> Sourced EpiInTm -> EpiInTm
>   EC :: Sourced Template -> [Sourced EpiInTm] -> EpiInTm
>   deriving Show

> data EpiExTm :: * where
>   EVS :: Sourced Template -> [Sourced EpiElim] -> EpiExTm
>   deriving Show

> data EpiElim :: * where
>   EA :: EpiInTm -> EpiElim
>   EJ :: Int -> EpiElim
>   deriving Show

> exampleEpiDoc :: EpiDoc
> exampleEpiDoc =
>   [  "" :~ Def {DataDef}
>        ("" :~ Sig [] ("" :~ DataConc ("" :~ "Nat") []))
>        ("" :~ Dial ("" :~ DataProb ("" :~ "Nat") [] [])
>          [  "" :~ ECons ("" :~ "zero") []
>          ,  "" :~ ECons ("" :~ "suc")
>            ["" :~ Sig []
>               ("" :~ VarConc ("" :~ "n") []
>                 (Just ("" :~ EEx (EVS ("" :~ "Nat") []))))]
>          ] [] []
>        )
>   ]