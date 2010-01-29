%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module ProofState.Induction where

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import DisplayLang.Naming

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.ProofState
> import ProofState.ProofKit

> import Cochon.DisplayCommands

%endif

\section{Induction on |Desc|}

> data Branch = ReadArgF
>             | ReadInd1



> dropSigUnit :: ProofState () -> ProofState ()
> dropSigUnit action = do
>   (_ :=>: goal) <- getGoal "dropSigUnit"
>   case goal of
>     PI UNIT _T -> do
>                   _TVoidtm <- bquoteHere (_T $$ A VOID)
>                   (t :=>: _) <- make $ "t" :<: _TVoidtm
>                   goIn 
>                   action
>                   goOut
>                   give' $ L $ K (N t)
>                   return ()
>     x -> throwError' $ "dropSigUnit: oops"

> introHyps :: Fwd Branch -> ProofState ()
> introHyps F0 = do 
>   dropSigUnit $ return ()
> introHyps (ReadInd1 :> bs) = do
>     (_ :=>: goal) <- getGoal "introHyps:Ind1"
>     sigmaToPi goal $ do
>       lambdaBoy "Px"
>       introHyps bs

> introHyps (ReadArgF :> bs) = do
>   introHyps bs

> introData :: Bwd Branch -> VAL -> ProofState ()
> introData branch DONE = dropSigUnit $ introHyps (branch <>> F0)

> introData branch (IND1 _D') = do
>   (_ :=>: goal) <- getGoal "introData:Ind1"
>   sigmaToPi goal $ do
>                    lambdaBoy "x"
>                    introData (branch :< ReadInd1) _D'
>                    return ()

> introData branch (ARG (ENUMT _X) _F) = do
>   (_ :=>: goal) <- getGoal "introData:Done"
>   sigmaToPi goal $ do
>     (_ :=>: goal) <- getGoal "introData:Done 2"
>     case goal of
>       PI _ _T -> do
>                  _Xtm <- bquoteHere _X
>                  _Ttm <- bquoteHere _T
>                  branches <- bquoteHere $ branchesOp @@ [ _X, _T]
>                  (m :=>: _) <- make $ "branches" :<: branches
>                  goIn
>                  (_ :=>: goal) <- getGoal "introData:Done 3"
>                  cases <- mkCases branch ZE goal _F
>                  give' $ cases
>                  goOut
>                  x <- lambdaBoy "x"
>                  give' $ N $ switchOp :@ [ _Xtm, NP x, _Ttm, N m ]
>                  return ()
            
> introData _ x = do
>   proofTrace $ "OOps: " ++ show x


> mkCases :: Bwd Branch -> VAL -> VAL -> VAL -> ProofState INTM
> mkCases _ _ UNIT _F = return VOID
> mkCases branch n (TIMES goal t) _F = do
>   goalTm <- bquoteHere goal
>   subgoalTm :=>: subgoal <- make $ "case" :<: goalTm
>   goIn 
>   introData  (branch :< ReadArgF) (_F $$ A n)
>   goOut 
>   cases <- mkCases branch (SU n) t _F
>   return $ PAIR (N subgoalTm) cases
> mkCases _ t v _ = error $ "mkCases: " ++ show t ++ "\n" ++ show v

> sigmaToPi :: VAL -> ProofState () -> ProofState ()
> sigmaToPi (PI (SIGMA _A _B) _T) action = do
>   let newGoal = PI _A . L . HF (fortran _B) $ \ a ->
>                 PI (_B $$ A a) . L . HF (fortran _T) $ \ b ->
>                 _T $$ A (PAIR a b)
>   _TPiTm <- bquoteHere newGoal
>   (t :=>: _) <- make $ "t" :<: _TPiTm
>   goIn
>   action
>   goOut
>   ab <- lambdaBoy "ab"
>   give' $ N (t  :$ A (N (P ab :$ Fst))
>                 :$ A (N (P ab :$ Snd)))
>   return ()
> sigmaToPi _ _ = throwError' "sigmaToPi: oops."


> induction :: RelName -> ProofState ()
> induction desc = do
>     _D <- resolveHere desc
>     case _D of 
>       _ := (DEFN (MU _ v) :<: _) -> do
>                    introData B0 v
>                    nextGoal
>       _ -> throwError' "induction: undefined Desc"

> import -> CochonTactics where
>   : (unaryNameCT  "induction"
>                   (\name -> induction name >> return "Simplification done.")
>       "induction <Desc> - simplify the result of an elimination on a Desc.")
