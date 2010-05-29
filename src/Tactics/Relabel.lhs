\section{Relabelling}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Tactics.Relabel where

> import Control.Applicative
> import Data.Traversable

> import Evidences.Rules
> import Evidences.Tm

> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm

> import Elaboration.ElabMonad
> import Elaboration.Elaborator

> import Kit.MissingLibrary

%endif

The |relabel| command changes the names of the pattern variables in a programming
problem. It takes an unelaborated application corresponding to the programming
problem, matches it against the existing arguments to determine the renaming,
and refines the proof state appropriately.

> relabel :: DExTmRN -> ProofState ()
> relabel (DP [(f, Rel 0)] ::$ ts) = do
>     _ :=>: tau <- getHoleGoal
>     case tau of
>         LABEL (N l) ty -> do
>             let Just (r, as) = splitSpine l
>             if f == (fst . last $ refName r)
>                 then do
>                     ts'  <- traverse unA ts
>                     n    <- matchArgs (pty r) (P r) as ts'
>                     ty'  <- bquoteHere ty
>                     g :=>: _ <- make ("relabel" :<: LABEL (N n) ty')
>                     give' (N g)
>                     goIn
>                 else  throwError' $ err "relabel: mismatched function name!"
>         _ -> throwError' $ err "relabel: goal is not a labelled type!"
> relabel _ =   throwError' $ err "relabel: malformed relabel target!"

> unA :: Elim a -> ProofState a
> unA (A a)  = return a
> unA _      = throwError' $ err "unA: not an A!"

> splitSpine :: NEU -> Maybe (REF, [VAL])
> splitSpine (P r) = return (r, [])
> splitSpine (n :$ A a) = do
>     (r, as) <- splitSpine n
>     return (r, as ++ [a])
> splitSpine _ = (|)

> matchArgs :: TY -> EXTM -> [VAL] -> [DInTmRN] -> ProofState EXTM
> matchArgs _ n []  []  = return n
> matchArgs _ _ []  _       = throwError' $ err "relabel: too many arguments!"
> matchArgs _ _ _   []      = throwError' $ err "relabel: too few arguments!"
> matchArgs (PI s t) n (a:as) (w : ws)  = do
>     wtm :=>: _  <- matchProb (s :>: (w, a))
>     matchArgs (t $$ A a) (n :$ A wtm) as ws
> matchArgs ty n as ts  = throwError' $ err "relabel: unmatched\nty ="
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "\nn =" ++ errInTm (N n)
>                              ++ err "\nas =" ++ map UntypedVal as
>                              ++ err "\nts =" ++ map UntypedTm ts         


The |matchProb| command matches a display term against a value and returns a
renamed term, with the pattern variables defined in the context.

> matchProb :: (TY :>: (DInTmRN, VAL)) -> ProofState (INTM :=>: VAL)

If the display term is a pattern variable, we can just create a corresponding
definition in the context.

> matchProb (ty :>: (DNP [(p, Rel 0)], v)) = do
>     ty'  <- bquoteHere ty
>     v'   <- bquoteHere v
>     make (p :<: ty')
>     goIn
>     neutralise =<< give v'

If it is an underscore then we make no changes to the value.

> matchProb (ty :>: (DU, v)) = do
>     v' <- bquoteHere v
>     return $ v' :=>: v

If it is a pair or void then we match the components.

> matchProb (SIGMA s t :>: (DPAIR w x, PAIR y z)) = do
>     wtm :=>: wv <- matchProb (s :>: (w, y))
>     xtm :=>: xv <- matchProb (t $$ A y :>: (x, z))
>     return (PAIR wtm xtm :=>: PAIR wv xv)

> matchProb (UNIT :>: (DVOID, VOID)) = return $ VOID :=>: VOID

If it is a tag (possibly applied to arguments) and needs to be matched against
an element of an inductive type, we match the tags and values.

> matchProb (ty@(MU l d) :>: (DTag s as, CON (PAIR t xs)))
>   | Just (e, f) <- sumlike d = do
>     ntm :=>: nv <- elaborate (Loc 0) (ENUMT e :>: DTAG s)
>     sameTag <- withNSupply $ equal (ENUMT e :>: (nv, t))
>     if sameTag
>         then do
>             atm :=>: av <- matchProb
>                            (descOp @@ [f t, ty] :>: (foldr DPAIR DVOID as, xs))
>             return $ CON (PAIR ntm atm) :=>: CON (PAIR nv av)
>         else throwError' $ err "relabel: mismatched tags!"

> matchProb (ty :>: (w, v)) = do
>     proofTrace $ "ty: "  ++ show ty
>     proofTrace $ "w: "   ++ show w
>     proofTrace $ "v: "   ++ show v
>     throwError' $ err "relabel: can't match"
>         ++ errTm w ++ err "with" ++ errTyVal (v :<: ty)


> import -> CochonTactics where
>   : unaryExCT "relabel" (\ ex -> relabel ex >> return "Relabelled.")
>       "relabel <pattern> - changes names of arguments in label to pattern"