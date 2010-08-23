\section{Operator DSL}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.OperatorDSL where

> import Control.Applicative
> import Control.Monad.Error

> import Evidences.Tm
> import {-# SOURCE #-} Evidences.Eval

> import Features.Features ()

%endif

\pierre{Crying for documentation (and more user-friendly syntax).}

Based on, but not quite the same as Edwin's experimental operator
DSEL, try this.

> data OpTree
>   = OLam (VAL -> OpTree)
>   | OPr OpTree
>   | OCase [OpTree]
>   | OCon OpTree
>   | OSet (Can VAL -> OpTree)
>   | ORet VAL
>   | OBarf

> oData :: [OpTree] -> OpTree
> oData = OCon . OPr . OCase 

> class OLams t where
>   oLams :: t -> OpTree
> instance OLams OpTree where
>   oLams = id
> instance OLams t => OLams (() -> t) where
>   oLams f = OLam $ \ _ -> oLams (f ())
> instance OLams t => OLams (VAL -> t) where
>   oLams = OLam . (oLams .)

> class OTup t where
>   oTup :: t -> OpTree
> instance OTup OpTree where
>   oTup = OLam . const
> instance OTup t => OTup (() -> t) where
>   oTup f = OPr . OLam $ \ _ -> oTup (f ())
> instance OTup t => OTup (VAL -> t) where
>   oTup = OPr . OLam . (oTup .)

> runOpTree :: OpTree -> [VAL] -> Either NEU VAL
> runOpTree (OLam f)  (x : xs)  = runOpTree (f x) xs
> runOpTree (OPr f)   (v : xs)  = runOpTree f (v $$ Fst : v $$ Snd : xs)
> runOpTree (OCase bs) (i : xs)   = (| (bs !!) (num i) |) >>= \ b -> runOpTree b xs where
>   num :: VAL -> Either NEU Int
>   num ZE      = (| 0 |)
>   num (SU n)  = (| (1+) (num n) |)
>   num (N e)   = Left e
> runOpTree (OCon f) (CON t : xs)  = runOpTree f (t : xs)
> runOpTree (OSet f) (C c :  xs)   = runOpTree (f c) xs
> runOpTree (ORet v)          xs   = Right (v $$$ map A xs)
> runOpTree _  (N e : xs)   = Left e


Grot! Why does the |Monad (Either e)| instance demand |(Error e)|? I shut it up.

> instance Error NEU where
>   strMsg = error

