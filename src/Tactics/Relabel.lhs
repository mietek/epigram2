\section{Relabelling}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Tactics.Relabel where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (foldr)
> import Data.Traversable

> import Evidences.Tm
> import Evidences.Utilities
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.Scope

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Definition
> import ProofState.Interface.Solving
> import ProofState.Interface.Lifting
> import ProofState.Interface.Parameter

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Elaboration.ElabMonad
> import Elaboration.Elaborator

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

A relabelling is a map from refrences to strings, giving a new name that should
be used for the reference.

> type Relabelling = Bwd (REF, String)

The |relabel| command changes the names of the pattern variables in a programming
problem. It takes an unelaborated application corresponding to the programming
problem, matches it against the existing arguments to determine the renaming,
and refines the proof state appropriately.

> relabel :: DExTmRN -> ProofState ()
> relabel (DP [(f, Rel 0)] ::$ ts) = do
>     tau' :=>: tau <- getHoleGoal
>     case tau of
>         LABEL (N l) ty -> do
>             let Just (r, as) = splitSpine l
>             unless (f == refNameAdvice r) $
>                 throwError' $ err "relabel: mismatched function name!"
>             ts'  <- traverse unA ts
>             rl   <- matchArgs (pty r) ts' as B0
>             es   <- getEntriesAbove
>             refineProofState (liftType es tau') (N .($:$ paramSpine es))
>             introLambdas rl (paramREFs es)
>         _ -> throwError' $ err "relabel: goal is not a labelled type!"
> relabel _ =   throwError' $ err "relabel: malformed relabel target!"

Once the refinement has been made, we need to introduce the hypotheses using
their new names. The |introLambdas| command takes a relabelling and the
references from the entries that were abstracted over, and introduces a
hypothesis corresponding to each reference with the reference's new name.

> introLambdas :: Relabelling -> [REF] -> ProofState ()
> introLambdas rl [] = return ()
> introLambdas rl (x:xs) = lambdaParam newName >> introLambdas rl xs
>   where
>     newName = case find ((x ==) . fst) rl of
>                   Just (_, s)  -> s
>                   Nothing      -> refNameAdvice x

> unA :: Elim a -> ProofState a
> unA (A a)  = return a
> unA _      = throwError' $ err "unA: not an A!"



> matchArgs :: TY -> [DInTmRN] -> [VAL] -> Relabelling -> ProofState Relabelling
> matchArgs _ []  []  rl  = return rl
> matchArgs _ []  _   _   = throwError' $ err "relabel: too few arguments!"
> matchArgs _ _   []  _   = throwError' $ err "relabel: too many arguments!"
> matchArgs (PI s t) (w:ws) (a:as) rl = do
>     rl'  <- matchProb (s :>: (w, a)) rl
>     matchArgs (t $$ A a) ws as rl'
> matchArgs ty ws as rl  = throwError' $ err "relabel: unmatched\nty ="
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "\nas =" ++ foldMap errVal as
>                              ++ err "\nws =" ++ foldMap errTm ws



> matchProb :: (TY :>: (DInTmRN, VAL)) -> Relabelling -> ProofState Relabelling

If we are matching two parameters, we can extend the relabelling after checking
that the reference has not already been given an inconsistent name.

> matchProb (ty :>: (DNP [(s, Rel 0)], NP (r@(_ := DECL :<: _)))) rl =
>     case find ((r ==) . fst) rl of
>         Nothing                   -> return (rl :< (r, s))
>         Just (_, t)  | s == t     -> return rl
>                      | otherwise  -> throwError' $
>             err ("matchProb: inconsistent names '" ++ s ++ "' and '" ++ t
>                         ++ "' for") ++ errRef r
>             

If the display term is an underscore then we make no changes to the relabelling.

> matchProb (ty :>: (DU, _)) rl = return rl

If it is a pair or void then we match the components.

> matchProb (SIGMA s t :>: (DPAIR w x, PAIR y z)) rl =
>     matchProb (s :>: (w, y)) rl >>= matchProb (t $$ A y :>: (x, z))

> matchProb (UNIT :>: (DVOID, VOID)) rl = return rl

If it is a tag (possibly applied to arguments) and needs to be matched against
an element of an inductive type, we match the tags and values.

> matchProb (ty@(MU l d) :>: (DTag s as, CON (PAIR t xs))) rl
>   | Just (e, f) <- sumlike d = do
>     ntm :=>: nv  <- elaborate (Loc 0) (ENUMT e :>: DTAG s)
>     sameTag      <- withNSupply $ equal (ENUMT e :>: (nv, t))
>     unless sameTag $ throwError' $ err "relabel: mismatched tags!"
>     matchProb (descOp @@ [f t, ty] :>: (foldr DPAIR DVOID as, xs)) rl

Similarly for indexed data types:

> matchProb (IMU l _I d i :>: (DTag s as, CON (PAIR t xs))) rl
>   | Just (e, f) <- sumilike _I (d $$ A i) = do
>     ntm :=>: nv  <- elaborate (Loc 0) (ENUMT e :>: DTAG s)
>     sameTag      <- withNSupply $ equal (ENUMT e :>: (nv, t))
>     unless sameTag $ throwError' $ err "relabel: mismatched tags!"
>     matchProb (idescOp @@ [_I, f t,
>         L $ "i" :. [.i. IMU (fmap (-$ []) l) (_I -$ []) (d -$ []) (NV i)] ]
>             :>: (foldr DPAIR DU as, xs)) rl

Lest we forget, tags may also belong to enumerations!

> matchProb (ENUMT e :>: (DTag s [], t)) rl = do
>   ntm :=>: nv <- elaborate (Loc 0) (ENUMT e :>: DTAG s)
>   sameTag <- withNSupply $ equal (ENUMT e :>: (nv, t))
>   unless sameTag $ throwError' $ err "relabel: mismatched tags!"
>   return rl

Nothing else matches? We had better give up.

> matchProb (ty :>: (w, v)) rl =  throwError' $ err "relabel: can't match"
>                                 ++ errTm w ++ err "with" ++ errTyVal (v :<: ty)


> import -> CochonTactics where
>   : unaryExCT "relabel" (\ ex -> relabel ex >> return "Relabelled.")
>       "relabel <pattern> - changes names of arguments in label to pattern"