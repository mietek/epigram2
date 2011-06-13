\section{Scope management}

Move to |ProofState.ProofContext|?

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, StandaloneDeriving #-}

> module ProofState.Edition.Scope where

> import Data.Foldable

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext

> import Evidences.Tm

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


\subsection{Extracting scopes as entries}


The |globalScope| function returns the parameters and definitions
available in the current development, not including the ones involved
in its construction.

> globalScope :: ProofContext -> Entries
> globalScope pc = foldMap aboveEntries (pcLayers pc)


The |inScope| function returns all parameters and definitions above
the cursor. These are all entries rightfully usable at the cursor's
location.

> inScope :: ProofContext -> Entries
> inScope pc@PC{pcAboveCursor=Dev{devEntries = es}} = globalScope pc <+> es




The |definitionsToImpl| function lists the entries above the cursor
that have been issued during elaboration of a programming problem
(Section~\ref{subsec:Elaborator.Elaborator.elab-prog-problem}). \pierre{That's
all I know about it, sorry about that.}

\pierre{This really is a hack. I hope it will disapear any time soon.}


> magicImplName = "impl"
>
> definitionsToImpl :: ProofContext -> [(Int, String, TY)]
> definitionsToImpl pc@PC{pcAboveCursor=Dev{devEntries=es}} = 
>     help (pcLayers pc) (params es)
>   where
>     help :: Bwd Layer -> [(Int, String, TY)] -> [(Int, String, TY)]
>     help B0 xs = xs
>     help (ls :< Layer{currentEntry=CDefinition d _}) xs
>         | (fst . last . defName $ d) == magicImplName = xs
>     help (ls :< l) xs = help ls (params (aboveEntries l) ++ xs)
>     params = foldMap param
>     param (EParam _ s t l)  = [(l,s,t)]
>     param _                 = []




\subsection{Manipulating entries as scopes}



We often need to turn the sequence of parameters under which we work
into the argument spine of a \(\lambda\)-lifted definition. Therefore,
let us extract such spine from a list of entries:

> params :: Entries -> [ (Tm {Body, Exp, n}) ]
> params es = herp es []
>   where herp :: Entries -> [ (Tm {Body, Exp, n}) ] -> [ (Tm {Body, Exp, n}) ]
>         herp B0 c = c
>         herp (ez :< (EParam _ s t l)) c = herp ez ((P (l, s, t) :$ B0) : c)
>         herp (ez :< _) c = herp ez c


> paramSpine :: Entries -> Bwd (Elim (Tm {Body, Exp, n}))
> paramSpine B0 = B0
> paramSpine (ez :< (EParam _ s t l)) = paramSpine ez :< A (P (l, s, t) :$ B0)
> paramSpine (ez :< _) = paramSpine ez

> params' :: Entries -> [ (Int, String, TY) ]
> params' es = herp es []
>   where herp :: Entries -> [ (Int, String, TY) ] -> [ (Int, String, TY) ]
>         herp B0 c = c
>         herp (ez :< (EParam _ s t l)) c = herp ez ((l, s, t) : c)
>         herp (ez :< _) c = herp ez c



Similarly, |applySpine| applies a reference to a given spine of
parameters, provided as a spine. These are the shared parameters of a
\(\lambda\)-lifted definition.

> applySpine :: EXP -> Entries -> EXP
> applySpine ref aus = ref $$$ paramSpine aus

