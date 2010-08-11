%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances,
>              PatternGuards, TupleSections #-}

> module Tactics.ShowHaskell where

> import Prelude hiding (any, foldl)

> import Data.List

> import Evidences.Tm

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofState

> import ProofState.Interface.ProofKit

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\section{Converting Epigram definitions to Haskell}

> dumpHaskell :: INTM :=>: VAL :<: TY -> ProofState String
> dumpHaskell (_ :=>: v :<: ty) = do
>     v'   <- bquoteHere v
>     ty'  <- bquoteHere ty
>     return $ "    ty   = " ++ showHaskell B0 ty' ++
>                  "\n    def  = " ++ showHaskell B0 v'


> class ShowHaskell a where
>     showHaskell :: Bwd String -> a -> String

> instance ShowHaskell REF where
>     showHaskell bs r = fst (mkLastName r)

> instance ShowHaskell (Tm {d, p} REF) where
>     showHaskell bs (L s)       = showHaskell bs s
>     showHaskell bs (C c)       = showHaskell bs c
>     showHaskell bs (NV i)      = "(NV " ++ maybe (show i) id (bs !. i) ++ ")"
>     showHaskell bs (N n)       = "(N " ++ showHaskell bs n ++ ")"
>     showHaskell bs (P r)       = showHaskell bs r
>     showHaskell bs (V i)       = "(V " ++ maybe (show i) id (bs !. i) ++ ")"
>     showHaskell bs (op :@ as)  = "(" ++ opName op ++ "Op :@ " ++ showHaskell bs as ++ ")"
>     showHaskell bs (f :$ a)    = "(" ++ showHaskell bs f ++ " :$ " ++ showHaskell bs a ++ ")"
>     showHaskell bs (t :? ty)   = "(" ++ showHaskell bs t ++ " :? " ++ showHaskell bs ty ++ ")"
>     showHaskell bs x           = error "showHaskell: can't show " ++ show x

> instance ShowHaskell (Scope p REF) where
>     showHaskell bs (x :. t)    = "(L $ " ++ show x ++ " :. [." ++ x ++ ". " ++
>                                      showHaskell (bs :< x) t ++ "])"
>     showHaskell bs (K t)       = "(LK " ++ showHaskell bs t ++ ")"
>     showHaskell bs x           = error "showHaskell: can't show " ++ show x

> instance ShowHaskell (Can (Tm {d, p} REF)) where
>     showHaskell bs Set         = "SET"
>     showHaskell bs (Pi _S (LK _T)) = "(ARR " ++ showHaskell bs _S ++ " " ++
>                                      showHaskell bs _T ++ ")"
>     showHaskell bs (Pi _S _T)  = "(PI " ++ showHaskell bs _S ++ " " ++
>                                      showHaskell bs _T ++ ")"
>     showHaskell bs (Con x)     = "(CON " ++ showHaskell bs x ++ ")"

>     showHaskell bs UId         = "UID"
>     showHaskell bs (Tag s)     = "(TAG " ++ show s ++ ")"
>     showHaskell bs (EnumT e)   = "(ENUMT " ++ showHaskell bs e ++ ")"
>     showHaskell bs Ze          = "ZE"
>     showHaskell bs (Su t)      = "(SU " ++ showHaskell bs t ++ ")"
>     showHaskell bs Unit        = "UNIT"
>     showHaskell bs Void        = "VOID"
>     showHaskell bs (Sigma _S _T) = "(SIGMA " ++ showHaskell bs _S ++ " " ++ showHaskell bs _T ++ ")"
>     showHaskell bs (Pair a b)  = "(PAIR " ++ showHaskell bs a ++ " " ++ showHaskell bs b ++ ")"
>     showHaskell bs Prop        = "PROP"
>     showHaskell bs (Prf p)     = "(PRF " ++ showHaskell bs p ++ ")"
>     showHaskell bs (All s t)   = "(ALL " ++ showHaskell bs s ++ " " ++ showHaskell bs t ++ ")"
>     showHaskell bs (And p q)   = "(AND " ++ showHaskell bs p ++ " " ++ showHaskell bs q ++ ")"
>     showHaskell bs Trivial     = "TRIVIAL"
>     showHaskell bs Absurd      = "ABSURD"
>     showHaskell bs (Inh t)     = "(INH " ++ showHaskell bs t ++ ")"
>     showHaskell bs (Wit t)     = "(WIT " ++ showHaskell bs t ++ ")"
>     showHaskell bs (Mu (l :?=: Id x))  = "(MU " ++ showHaskell bs l ++ " " ++ showHaskell bs x ++ ")"
>     showHaskell bs (IMu (l :?=: (Id ii :& Id x)) i) = "(IMU " ++ showHaskell bs l ++ " " ++ showHaskell bs ii ++ " " ++ showHaskell bs x ++ " " ++ showHaskell bs i ++ ")"
>     showHaskell bs (EqBlue ss tt) = "(EQBLUE " ++ showHaskell bs ss ++ " " ++ showHaskell bs tt ++ ")"
>     showHaskell bs (Monad s t) = "(MONAD " ++ showHaskell bs s ++ " " ++ showHaskell bs t ++ ")"
>     showHaskell bs (Return x) = "(RETURN " ++ showHaskell bs x ++ ")"
>     showHaskell bs (Composite t) = "(COMPOSITE " ++ showHaskell bs t ++ ")"
>     showHaskell bs (Nu (l :?=: Id t)) = "(NU " ++ showHaskell bs l ++ " " ++ showHaskell bs t ++ ")"
>     showHaskell bs (CoIt d sty f s) = "(COIT " ++ showHaskell bs d ++ " " ++ showHaskell bs sty ++ " " ++ showHaskell bs f ++ " " ++ showHaskell bs s ++ ")"
>     showHaskell bs (Label l t) = "(LABEL " ++ showHaskell bs l ++ " " ++ showHaskell bs t ++ ")"
>     showHaskell bs (LRet t) = "(LRET " ++ showHaskell bs t ++ ")"
>     showHaskell bs (Quotient x r p) = "(QUOTIENT " ++ showHaskell bs x ++ " " ++ showHaskell bs r ++ " " ++ showHaskell bs p ++ ")"
>     showHaskell bs RSig = "RSIG"
>     showHaskell bs REmpty = "REMPTY"
>     showHaskell bs (RCons s i t) = "(RCONS " ++ showHaskell bs s ++ " " ++ showHaskell bs i ++ " " ++ showHaskell bs t ++ ")"
>     showHaskell bs (Record (l :?=: Id s)) = "(RECORD " ++ showHaskell bs l ++ " " ++ showHaskell bs s ++ ")"
>
>     showHaskell bs x           = error "showHaskell: can't show " ++ show x

> instance ShowHaskell (Elim (Tm {d, p} REF)) where
>     showHaskell bs (A a)       = "(A " ++ showHaskell bs a ++ ")"
>     showHaskell bs Out         = "Out"
>
>     showHaskell bs Fst         = "Fst"
>     showHaskell bs Snd         = "Snd"
>     showHaskell bs (Call l)    = "(CALL " ++ showHaskell bs l ++ ")"
>
>     showHaskell bs x           = error "showHaskell: can't show " ++ show x

> instance ShowHaskell a => ShowHaskell [a] where
>     showHaskell bs xs = "[" ++ intercalate ", " (map (showHaskell bs) xs) ++ "]"

> instance ShowHaskell a => ShowHaskell (Maybe a) where
>     showHaskell bs Nothing = "Nothing"
>     showHaskell bs (Just x) = "(Just " ++ showHaskell bs x ++ ")"

> instance (ShowHaskell a, ShowHaskell b) => ShowHaskell (a :>: b) where
>     showHaskell bs (ty :>: t) = "(" ++ showHaskell bs ty ++ " :>: " ++ showHaskell bs t ++ ")"

> import -> CochonTactics where
>   : unaryExCT "haskell" (\ t -> elabInfer' t >>= dumpHaskell)
>       "haskell - renders an Epigram term as a Haskell definition."