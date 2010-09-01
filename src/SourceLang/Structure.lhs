\section{Structure}
\label{sec:SourceLang.Structure}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module SourceLang.Structure where

> import Data.Foldable
> import Data.Traversable

> import Evidences.Tm
> import DisplayLang.Name

%endif

This is an implementation of the proposed @.epi@ file structure, based on
Conor's notes. Everything is parameterised by a type for terms, so we get a
bunch of traversable functors. This means we can't easily enforce invariants
on term direction, but the resulting simplification is probably worth it.

A \emph{document} is a list of \emph{constructions} (using slightly different
terminology because we use ``development'' to mean something else in the
proof state).

> type EpiDoc t = [Construction t]

> data Construction t = LetConstr (Decl t) (Maybe (Refinement t))
>     deriving (Functor, Foldable, Traversable, Show)

> data Decl t = Decl  {  declHyps      :: [Decl t]
>                     ,  declTemplate  :: String
>                     ,  declType      :: t
>                     }
>     deriving (Functor, Foldable, Traversable, Show)

> data Refinement t = Refinement  {  refProblem  :: t
>                                 ,  refTactic   :: Tactic t
>                                 ,  refWhere    :: Block t
>                                 }
>     deriving (Functor, Foldable, Traversable, Show)

> data Tactic t  =  ReturnTac  t
>                |  ByTac      t (Block t)
>                |  ShedTac
>     deriving (Functor, Foldable, Traversable, Show)

> type Block t = [Refinement t]

When we store terms, we potentially have three different representations: a
|String| provided by the user, the result of parsing it to display syntax,
and the result of elaborating it as an evidence term.

> type Lexed       =  String
> type Parsed      =  (String, DInTmRN)
> type Elaborated  =  (String, DInTmRN, INTM)