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

> import -> CochonTacticsCode where
>     defineCTactic :: DExTmRN -> DInTmRN -> ProofState String
>     defineCTactic rl tm = do
>         relabel rl
>         elabGiveNext (DLRET tm)
>         return "Hurrah!"

> import -> CochonTactics where
>   : (simpleCT
>      "define"
>      (| (| (B0 :<) tokenExTm |) :< (%keyword KwDefn%) tokenInTm |)
>      (\ [ExArg rl, InArg tm] -> defineCTactic rl tm)
>      "define <prob> := <term> - relabels and solves <prob> with <term>.")


\subsection{The By gadget}

The By gadget, written |<=|, invokes elimination with a motive, then simplifies
the methods and moves to the first subgoal remaining.

> import -> CochonTacticsCode where
>     byCTactic :: Maybe RelName -> DExTmRN -> ProofState String
>     byCTactic n e = do
>         elimCTactic n e
>         optional problemSimplify            -- simplify first method
>         many (goDown >> problemSimplify)    -- simplify other methods
>         many goUp                           -- go back up to motive
>         optional seekGoal                   -- jump to goal
>         return "Eliminated and simplified."

> import -> CochonTactics where
>   : (simpleCT
>     "<="
>     (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
>                                               |id tokenAscription |)|)
>     (\ [n,e] -> byCTactic (argOption (unDP . argToEx) n) (argToEx e))
>     "<= [<comma>] <eliminator> - eliminates with a motive.")


\subsection{The Refine gadget}

The Refine gadget relabels the programming problem, then either defines it
or eliminates with a motive.

> import -> CochonTactics where
>   : (simpleCT
>     "refine"
>     (|(|(B0 :<) tokenExTm|) :< (|id (%keyword KwEq%) tokenInTm
>                                 |id (%keyword KwBy%) tokenExTm
>                                 |id (%keyword KwBy%) tokenAscription
>                                 |)
>      |)
>     (\ [ExArg rl, arg] -> case arg of
>         InArg tm -> defineCTactic rl tm
>         ExArg tm -> relabel rl >> byCTactic Nothing tm)
>     ("refine <prob> =  <term> - relabels and solves <prob> with <term>.\n" ++
>      "refine <prob> <= <eliminator> - relabels and eliminates with a motive."))


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
