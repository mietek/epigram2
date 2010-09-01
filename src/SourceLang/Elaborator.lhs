\section{Elaborator}
\label{sec:SourceLang.Elaborator}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module SourceLang.Elaborator where

> import Control.Applicative
> import Data.Traversable

> import Evidences.Tm
> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Elaboration.ElabProb
> import Elaboration.ElabMonad
> import Elaboration.MakeElab

> import SourceLang.Structure

%endif

Here we explain how to elaborate constructions. The elaborator is going to need
a lot of work in order to actually run these definitions.

First things first: to elaborate a term, we just use |subElab| defined before.

> elabTerm :: Loc -> TY -> Parsed -> Elab Elaborated
> elabTerm loc ty (s, tm) = do
>     etm :=>: _ <- subElab loc (ty :>: tm)
>     return (s, tm, etm)

The following cases need some thought about exactly what elaboration should do.

> elabConstr :: Construction Parsed -> Elab (Construction Elaborated)
> elabConstr (LetConstr decl mref) = do
>     decl' <- elabDecl decl
>     return (LetConstr decl' Nothing)

> elabDecl :: Decl Parsed -> Elab (Decl Elaborated)
> elabDecl (Decl hyps x ty) =
>     (| Decl (traverse elabDecl hyps) ~x (elabTerm (Loc 0) SET ty) |)

> elabRefinement :: Refinement Parsed -> Elab (Refinement Elaborated)
> elabRefinement (Refinement prob tac wbk) = undefined