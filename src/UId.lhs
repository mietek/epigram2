\section{UId}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module UId where

%endif

Formation rule:

\begin{prooftree}
\AxiomC{}
\RightLabel{UId-formation}
\UnaryInfC{|Set :>: UId|}
\end{prooftree}

Introduction rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{UId-intro-1}
\UnaryInfC{|UId :>: Tag s|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|s1 == s2|}
\RightLabel{UId-intro-2}
\UnaryInfC{|UId :>: (Tag s1 == Tag s2)|}
\end{prooftree}

Equality rules:

< eqGreen(UId, Tag s1, UId, Tag s2) :-> Trivial -- if s1 == s2
< eqGreen(UId, Tag s1, UId, Tag s2) :-> Absurd  -- otherwise

> import -> CanConstructors where
>   UId    :: Can t
>   Tag    :: String -> Can t

> import -> CanPats where
>   pattern UID = C UId
>   pattern TAG s = C (Tag s)

> import -> TraverseCan where
>   traverse f UId          = (|EnumU|)
>   traverse f (Tag s)      = (|(Tag s)|)

> import -> CanPretty where
>   prettyCan UId      = text "Uid"
>   prettyCan (Tag s)  = text ('@':s)

> import -> CanTyRules where
>   canTy _  (Set :>: UId)    = return UId
>   canTy _  (UId :>: Tag s)  = return (Tag s)

> import -> OpRunEqGreen where
>   opRunEqGreen [UID,TAG s1,UID,TAG s2] | s1 == s2 = Right $ TRIVIAL
>   opRunEqGreen [UID,TAG _,UID,TAG _] = Right $ ABSURD
