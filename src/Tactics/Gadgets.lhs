\section{Programming Gadgets}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.Gadgets where

%endif



\subsection{The Return gadget}

> import -> CochonTactics where
>   : unaryInCT "=" (\tm -> elabGiveNext (DLRET tm) >> return "Ta.")
>       "= <term> - solves the programming problem by returning <term>."


\subsection{The Define gadget}

> import -> CochonTactics where
>   : (simpleCT
>      "define"
>      (| (| (B0 :<) tokenExTm |) :< (%keyword KwDefn%) tokenInTm |)
>      (\ [ExArg rl, InArg tm] -> do
>          relabel rl
>          elabGiveNext (DLRET tm)
>          return "Hurrah!")
>      "define <prob> := <term> - relabels and solves <prob> with <term>")


\subsection{The By gadget}

The By gadget, written |<=|, invokes elimination with a motive, then simplifies
the methods and moves to the first subgoal remaining.

> import -> CochonTactics where
>   : (simpleCT
>     "<="
>     (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
>                                               |id tokenAscription |)|)
>     (\ [n,e] -> do
>         elimCTactic (argOption (unDP . argToEx) n) (argToEx e)
>         optional problemSimplify            -- simplify first method
>         many (goDown >> problemSimplify)    -- simplify other methods
>         many goUp                           -- go back up to motive
>         goDown                              -- go down to first method
>         optional seekGoal                   -- jump to goal
>         return "Eliminated and simplified."
>     )
>     "<= [<comma>] <eliminator> - eliminates with a motive.")


\subsection{The Solve gadget}

> import -> CochonTactics where
>     : simpleCT
>         "solve"
>         (| (| (B0 :<) tokenName |) :< tokenInTm |)
>         (\ [ExArg (DP rn ::$ []), InArg tm] -> do
>             (ref, spine, _) <- resolveHere rn
>             _ :<: ty <- inferHere (P ref $:$ toSpine spine)
>             _ :=>: tv <- elaborate' (ty :>: tm)
>             tm' <- bquoteHere tv -- force definitional expansion
>             solveHole ref tm'
>             return "Solved."
>           )
>         "solve <name> <term> - solves the hole <name> with <term>."
