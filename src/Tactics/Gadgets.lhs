\section{Programming Gadgets}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.Gadgets where

> import Tactics.Elimination

%endif



\subsection{The |Return| gadget}

> import -> CochonTactics where
>   : unaryInCT "=" (\tm -> elabGiveNext (DLRET tm) >> return "Ta.")
>       "= <term> - solves the programming problem by returning <term>."



\subsection{The |By| gadget}

> import -> CochonTactics where
>   : (simpleCT
>     "<="
>     (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
>                                               |id tokenAscription |)|)
>     (\[n,e] -> elimCTactic (argOption (unDP . argToEx) n) (argToEx e))
>     "<= [<comma>] <eliminator> - eliminates with a motive.")
