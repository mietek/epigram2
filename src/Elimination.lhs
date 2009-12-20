%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module Elimination where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable hiding (sequence_)
> import Data.List
> import Data.Traversable hiding (sequence)

> import BwdFwd
> import Developments
> import Naming
> import PrettyPrint
> import Root
> import Rooty
> import Rules
> import Tm
> import qualified Tactics as Tac
> import ProofState

> import MissingLibrary

%endif

\section{Elimination with a Motive}



%if false
[tested by testChunk]
%endif

> chunkGoal :: ProofState ([REF], TY)
> chunkGoal = do
>     rs <- many $ lambdaBoy "chunk"
>     (_ :=>: goal) <- getGoal "chunkGoal"
>     return (rs, goal)

We might want to generalize this matcher to non-P stuffs. However,
it's a hell to write the type of what will get out.

%if false
[trusted]
%endif

> matchArgs :: Elim (Tm {In, VV} REF) -> [REF]
> matchArgs (A (N (P p :$ args))) = p : matchArgs args
> matchArgs (A (N (P p))) = [p]
> matchArgs _ = []


%if false
[trusted]
%endif

> getGoal :: String -> ProofState (INTM :=>: TY)
> getGoal s = do
>     tip <- getDevTip
>     case tip of
>       Unknown (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       Defined _ (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       _ -> throwError' $ "getGoal: fail to match a goal in "
>                          ++ s

%if false
[tested by testCheckElim]
%endif

> checkElim :: [a] -> REF -> ProofState (REF, [REF], [REF])
> checkElim ctxt e@(_ := (DEFN v) :<: ty) = do
>     -- Explore e by making it a subgoal
>     -- XXX: we should open a Module here and throw it away
>     ty' <- bquoteHere ty
>     make $ "elim" :<: ty'
>     goIn
>     -- Abstract over the internal hypotheses
>     sequence_ $ map (const $ lambdaBoy "ctxt") ctxt 
>     -- Grab the motive P
>     motive <- lambdaBoy "motive"
>     -- Grab the methods M P
>     methods <- many $ lambdaBoy "method"
>     -- Grab the target
>     (_ :=>: target) <- getGoal "checkElim"
>     case target of 
>       N ((P p) :$ args) -> do
>         -- The target must apply things to the motive
>         case p == motive of
>           False -> throwError' "checkElim: elimination ill-defined, applied to another function"
>           True -> do
>                   -- Grab the arguments of the motive
>                  let targetArgs = matchArgs args 
>                  -- Close the analysis by leaving the development (opened)
>                  -- XXX: see point above on Module
>                  goOut
>                  -- Return the results
>                  return (motive, methods, targetArgs)
>       _ -> throwError' $ "checkElim: elimination ill-defined, not using the motive"

%if false
[tested by testCheckMotive]
%endif

> checkMotive :: REF -> ProofState [REF]
> checkMotive motive = do
>     -- Explore the motive by making it a subgoal
>     -- XXX: This should be replaced by a thrown away Module
>     tyP <- bquoteHere $ pty motive
>     make $ "P" :<: tyP
>     goIn
>     -- Grab the arguments of the motive
>     motiveHyps <- many $ lambdaBoy "motiveHyps"
>     -- Check that the target is SET 
>     (_ :=>: SET) <- getGoal "checkMotive"
>     -- Close the analysis by closing the development
>     -- XXX: Again, Module story
>     goOut
>     -- Return the results
>     return motiveHyps


%if false
[untested]
%endif

> checkMethods :: [REF] -> ProofState ()
> checkMethods methods =
>     -- We ought to check methods are of type:
>     -- M P :: (motiveHyps -> Set) -> Set
>     return ()

%if false
[tested by testMMotive]
%endif

> mkMotive :: REF -> [REF] -> [REF] -> [REF] -> TY -> ProofState INTM
> mkMotive p@(_ := DECL :<: ty) motiveHyps motiveArgs internHyps goal = do
>     -- Now, it's serious, we make P
>     tyP <- bquoteHere ty
>     motive <- make $ "P" :<: tyP
>     goIn
>     -- Introduce hypotheses
>     args <- sequence $ map (const $ lambdaBoy "motiveHyp") motiveHyps
>     -- Make Pi over internal hypotheses
>     sequence_ $ map (\(_ := DECL :<: ty) -> do
>                      ty' <- bquoteHere ty
>                      piBoy ("delta" :<: ty')) internHyps
>     -- Make the list of equality constraints
>     case (length args == length motiveArgs) of
>       False -> throwError' "mkMotive: distinct number of arguments"
>       True -> do
>               constraints <- bquoteHere
>                              $ Data.List.foldl ARR goal -- XXX: goal should be applied
>                              $ map (\(i,t) -> PRF (EQBLUE (pty i :>: NP i) (pty t :>: NP t)))
>                              $ zip args motiveArgs
>               -- Make the term
>               give constraints

> applyElim :: [a] -> REF -> INTM -> [REF] -> [REF] -> [REF] -> ProofState ()
> applyElim internHyps e motive motiveArgs methods elimArgs = do
>     -- Make subgoal
>     methods <- sequence $ map (\(_ := DECL :<: ty) -> do
>                                  ty <- bquoteHere ty
>                                  make ("m" :<: ty)) methods
>     -- Make lambda for internal hypotheses
>     sequence_ $ map (\_ -> lambdaBoy "internHyps") internHyps
>     -- Get the goal, to feed to the Tactics
>     (_ :=>: termType) <- getGoal "applyElim"
>     -- Solve the elim problem
>     term <- withRoot mkTerm
>     give term
>     return ()
>         where mkTerm root = e $## (motive :
>                                   (map NP methods)
>                                ++ (map NP elimArgs)
>                                ++ (map (\t -> refl $## [ bquote B0 (pty t) root
>                                                        , NP t ]) motiveArgs))
>                             
     

> elim :: REF -> ProofState ()
> elim e = do
>     (internHyps, goal) <- chunkGoal
>     (motive, methods, motiveArgs) <- checkElim internHyps e
>     motiveHyps <- checkMotive motive
>     checkMethods methods
>     motive <- mkMotive motive motiveHyps motiveArgs internHyps goal
>     applyElim internHyps e motive motiveArgs methods motiveArgs
