\section{The distiller}
\label{sec:Distillation.Distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Distiller where

> import Evidences.Tm
> import Evidences.NameSupply

> import DisplayLang.DisplayTm
> import DisplayLang.Name

%endif


> distill :: TY :>: EXP -> Fresh (DInTmRN :=>: VAL)
> distill = undefined