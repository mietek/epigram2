%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

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
> import ProofState

> import MissingLibrary

%endif

\section{Elimination with a Motive}



%if false
[tested by testChunk]
%endif

> chunkGoal :: ProofState ([REF], INTM)
> chunkGoal = do
>     rs <- many $ lambdaBoy "chunk"
>     (goal :=>: _) <- getGoal "chunkGoal"
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
[tested by testCheckElim]
%endif

> checkElim :: [a] -> INTM -> ProofState ([REF], REF, [REF], [REF])
> checkElim ctxt ty = 
>     draftModule "checkElim" (do
>     -- Explore e by making it a subgoal
>     make $ "elim" :<: ty
>     goIn
>     -- Abstract over the internal hypotheses
>     motiveCtxt <- sequence $ map (const $ lambdaBoy "ctxt") ctxt 
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
>                  -- Abandon the development
>                  goOut
>                  -- Return the results
>                  return (motiveCtxt, motive, methods, targetArgs)
>       _ -> throwError' $ "checkElim: elimination ill-defined, not using the motive")

%if false
[tested by testCheckMotive]
%endif

> checkMotive :: REF -> ProofState [REF]
> checkMotive motive = 
>     draftModule "checkMotive" (do
>     -- Explore the motive by making it a subgoal
>     tyP <- bquoteHere $ pty motive
>     make $ "P" :<: tyP
>     goIn
>     -- Grab the arguments of the motive
>     motiveHyps <- many $ lambdaBoy "motiveHyps"
>     -- Check that the target is SET 
>     (_ :=>: SET) <- getGoal "checkMotive"
>     -- Abandon the development
>     goOut
>     -- Return the results
>     return motiveHyps)


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

> mkMotive :: [REF] -> REF -> [REF] -> [REF] -> [REF] -> INTM -> ProofState INTM
> mkMotive motiveCtxt p@(_ := DECL :<: ty) motiveHyps motiveArgs goalCtxt goal = do
>     -- Now, it's serious, we make P
>     tyP <- bquoteHere ty
>     motive <- make $ "P" :<: tyP
>     goIn
>     -- Introduce hypotheses
>     args <- sequence $ map (const $ lambdaBoy "motiveHyp") motiveHyps
>     -- Make Pi over internal hypotheses
>     delta <- sequence $ map (\(_ := DECL :<: ty) -> do
>                              ty' <- bquoteHere ty
>                              piBoy ("delta" :<: ty')) goalCtxt
>     -- Make the list of equality constraints
>     constraints <- bquoteHere
>                    $ Data.List.foldr ARR (evTm $ rGoal delta) 
>                    $ map (\(i,t) -> PRF (EQBLUE (pty i :>: NP i) (pty t :>: NP t)))
>                    $ zip args (rMotiveArgs delta)
>     -- Make the term
>     give constraints
>          where rGoal delta = renameVars goal $ zip goalCtxt delta
>                rMotiveArgs delta = map (\m -> unP $ renameVars (P m) (motiveCtxtDelta delta)) motiveArgs
>                motiveCtxtDelta delta = zip motiveCtxt delta
>                unP :: Tm {d,TT} REF -> REF
>                unP (P x) = x

> applyElim :: [REF] -> (INTM :>: INTM) -> [REF] -> INTM -> [REF] -> [REF] -> ProofState ()
> applyElim internHyps (ty :>: e) motiveCtxt motive motiveArgs methods = do
>     -- Make subgoal
>     methods <- sequence $ map (\m -> do
>                                 ty <- bquoteHere $ pty m
>                                 make ("method" :<:  ty)) methods
>     -- Solve the elim problem
>     term <- withRoot (mkTerm methods)
>     (goal :=>: _) <- getGoal "applyElim"
>     give term
>     return ()
>         where mkTerm methods root = (e :? ty) $## (map NP internHyps
>                                        ++ [motive]
>                                        ++ methods
>                                        ++ (map NP internHyps) -- (map NP rMotiveArgs) -- 
>                                        ++ (map (\t -> (P refl) $## [ bquote B0 (pty t) root
>                                                                    , NP t ]) rMotiveArgs))
>               rMotiveArgs = map (\m -> unP $ renameVars (P m) motiveCtxtInternHyps) motiveArgs
>               motiveCtxtInternHyps = zip motiveCtxt internHyps
>               unP :: Tm {d,TT} REF -> REF
>               unP (P x) = x

     

> elim :: (INTM :>: INTM) -> ProofState ()
> elim (t :>: e) = do
>     (internHyps, goal) <- chunkGoal
>     (motiveCtxt, motive, methods, motiveArgs) <- checkElim internHyps t
>     motiveHyps <- checkMotive motive
>     checkMethods methods
>     motive <- mkMotive motiveCtxt motive motiveHyps motiveArgs internHyps goal
>     applyElim internHyps (t :>: e) motiveCtxt motive motiveArgs methods 

> renameVars :: Tm {d,TT} REF -> [(REF,REF)] -> Tm {d,TT} REF
> renameVars tm assocList =
>     fmap rename tm
>         where rename r = case r `lookup` assocList of
>                            Nothing -> r
>                            Just r' -> r'