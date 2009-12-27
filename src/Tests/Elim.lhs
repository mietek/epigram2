> module Tests.Elim where

> import Control.Monad.State
> import Control.Applicative
> import Data.List

> import Root
> import BwdFwd
> import DevLoad
> import Developments
> import Elaborator
> import ProofState
> import Elimination
> import Parsley
> import PrettyPrint
> import Lexer
> import TmParse
> import Tm
> import Rules

> import Debug.Trace

> fromRight :: Either a b -> b
> fromRight (Left x) = error "fromRight: haha!"
> fromRight (Right x) = x



> testChunkTerms =  [ "( X : * ) -> X"
>                   , "( X : * ) ( t : X -> X ) ( y : X ) -> t y"
>                   , "( X : * ) ( Y : * )" ++
>                     "( t : X -> Y -> X )" ++
>                     "( y : X ) ( z : Y )  -> t y z"
>                   ]

> testChunk = 
>     Prelude.sequence_ $
>     map (\tm -> 
>         let Right tm' = parse tokenize tm
>             Right tm2 = parse (termParse B0) tm'
>             r = evalStateT (introTm tm2) emptyContext
>         in do
>           putStrLn $ "\n" ++ show tm 
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x@(hs, t) -> do
>                 putStrLn "Internal hyp.: "
>                 sequence_ $ map (putStrLn . show) hs
>                 putStrLn "Goal:"
>                 putStrLn $ show t)
>     testChunkTerms
>     where introTm tm = do
>               make ("" :<: tm)
>               goIn
>               r <- chunkGoal 
>               return r

> testCheckElimTerms = [ ("(N : *)(x : N)(P : N -> *) -> P x", [(),()])
>                      , ("(N : *)(Z : *)(x : N)(y : Z)(P : N -> Z -> *) -> P x y", [(),(),(),()])
>                      , ("(N : *)(x : N)(z : N)(P : N -> *) (pz : P z) -> P x", [(),(),()])
>                      ]


> testCheckElim = 
>     Prelude.sequence_ $
>     map (\(ty, ctxt) -> 
>         let Right ty' = parse (termParse B0) $ fromRight $ parse tokenize ty
>             r = evalStateT (checkElim ctxt ty') emptyContext
>         in do
>           putStrLn $ "\n" ++ show ty 
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x@(_, motive, methods, targets) -> do
>                 putStrLn "Motive: "
>                 putStrLn $ show motive
>                 putStrLn "Methods:"
>                 sequence_ $ map (putStrLn . show) methods
>                 putStrLn "Args:"
>                 sequence_ $ map (putStrLn . show) targets)
>     testCheckElimTerms

> testCheckElimTerms2 = [ ("Switch",[(),()])
>                       , ("split",[(),(),()])
>                       , ("elimOp",[(),()]) ]

> testCheckElim2 = 
>     Prelude.sequence_ $
>     map (\(tm,ctxt) -> 
>         let Just op = find (\o -> opName o == tm) operators
>             ty = opType (B0 :< ("a",0),0) op
>             ty' = bquote B0 ty ((B0 :< ("a",0),0) :: Root)
>             r = evalStateT (checkElim ctxt ty') emptyContext
>         in do
>           putStrLn $ "\n" ++ show tm
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x@(_, motive, methods, targets) -> do
>                 putStrLn "Motive: "
>                 putStrLn $ show motive
>                 putStrLn "Methods:"
>                 sequence_ $ map (putStrLn . show) methods
>                 putStrLn "Args:"
>                 sequence_ $ map (putStrLn . show) targets)
>     testCheckElimTerms2


These are not quite motive signature, but that's fine for this test:

> testCheckMotiveTerms = [ "(N : *)(n : N) -> *"
>                        , "(N : *)(n : N)(m : N) -> *"
>                        , "(N : *)(Z : *)(n : N)(z : Z) -> *"
>                        ]

> testCheckMotive =
>     Prelude.sequence_ $
>     map (\ty -> 
>         let Right ty' = parse (termParse B0) $ fromRight $ parse tokenize ty
>             name = [("e",1000)] := (DECL :<: evTm ty')
>             r = evalStateT (checkMotive name) emptyContext
>         in do
>           putStrLn $ "\n" ++ show ty 
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x@(hyps) -> do
>                 putStrLn "Hypotheses:"
>                 sequence_ $ map (putStrLn . show) hyps)
>     testCheckMotiveTerms

> testCheckMotiveTerms2 = [ ("Switch",[(),()])
>                         , ("split",[(),(),()])
>                         , ("elimOp",[(),()]) ]

> testCheckMotive2 = 
>     Prelude.sequence_ $
>     map (\(tm,ctxt) -> 
>         let Just op = find (\o -> opName o == tm) operators
>             ty = opType (B0 :< ("a",0),0) op
>             ty' = bquote B0 ty ((B0 :< ("a",0),0) :: Root)
>             r = evalStateT (checkMotiveWrap ctxt ty') emptyContext
>         in do
>           putStrLn $ "\n" ++ show tm
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x@(motiveHyps) -> do
>                 putStrLn "Motive hyps: "
>                 sequence_ $ map (putStrLn . show) motiveHyps)
>     testCheckMotiveTerms2
>         where checkMotiveWrap internHyps e = do
>                   (_, motive, methods, motiveArgs) <- checkElim internHyps e
>                   motiveHyps <- checkMotive motive
>                   return motiveHyps


> testMkMotiveTerms = [ ("(N : *) -> N",
>                        "(N : *)(P : N -> *)(x : N) -> P x")
>                     ]

> {-
>                     , ("",
>                        "(N : *)(Z : *)(x : N)(y : Z)(P : N -> Z -> *) -> P x y")
>                     , ("",
>                        "(N : *)(x : N)(z : N)(P : N -> *) (pz : P z) -> P x")
> -}

> testMkMotive =
>     Prelude.sequence_ $
>     map (\(goal,eTy) -> 
>         let Right goal' = parse (termParse B0) $ fromRight $ parse tokenize goal
>             Right eTy' = parse (termParse B0) $ fromRight $ parse tokenize eTy
>             r = evalStateT (test goal' eTy') emptyContext
>         in do
>           putStrLn $ "\n" ++ show goal
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x -> do
>                 putStrLn $ show x)
>     testMkMotiveTerms
>         where test tm e = do
>                           make ("" :<: tm)
>                           goIn
>                           (internHyps, goal) <- chunkGoal
>                           (motiveCtxt, motive, methods, motiveArgs) <- checkElim internHyps e
>                           motiveHyps <- checkMotive motive
>                           checkMethods methods
>                           motive <- mkMotive motiveCtxt motive motiveHyps motiveArgs internHyps goal
>                           return motive


> testMkMotiveTerms2 = [-- ("Switch",[(),()],"(e : EnumU)(x : EnumT e) -> x")
>                      {- , -} ("split",[(),(),()], "(A : *)(B : A -> *)(t : (A ; B)) -> t") ]
>                      -- , ("elimOp",[(),()],"(D : Desc)(v : Mu D) -> v") ]

> testMkMotive2 = 
>     Prelude.sequence_ $
>     map (\(tm,ctxt,g) -> 
>         let Just op = find (\o -> opName o == tm) operators
>             Right goal = parse (termParse B0) $ fromRight $ parse tokenize g
>             ty = opType (B0 :< ("a",0),0) op
>             ty' = bquote B0 ty ((B0 :< ("a",0),0) :: Root)
>             r = evalStateT (checkMotiveWrap goal ctxt ty') emptyContext
>         in do
>           putStrLn $ "\n" ++ show tm
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right x@(motiveHyps) -> do
>                 putStrLn "Motive: "
>                 putStrLn $ show motiveHyps)
>     testMkMotiveTerms2
>         where checkMotiveWrap goal internHyps e = do
>                   make $ "goal" :<: goal
>                   goIn
>                   (internHyps, goal) <- chunkGoal
>                   (motiveCtxt, motive, methods, motiveArgs) <- checkElim internHyps e
>                   motiveHyps <- checkMotive motive
>                   motive <- mkMotive motiveCtxt motive motiveHyps motiveArgs internHyps goal
>                   return motive

> testElimTerms = [-- ("Switch",[()],"(e : EnumU)(x : EnumT e) -> x")
>                  {- , -} ("split",[], "(A : *)(B : A -> *)(t : (A ; B)) -> t") 
>                  , ("split", [], "(A : *)(B : A -> *)(a : A) -> a")
>                  , ("split", [], "(A : *)(B : A -> *)(b : B) -> b") ]
>                   -- , ("elimOp",[()],"(D : Desc)(v : Mu D) -> v") ]

> testElim = 
>     Prelude.sequence_ $
>     map (\(tm,ctxt,g) -> 
>         let Just op = find (\o -> opName o == tm) operators
>             Right goal = parse (termParse B0) $ fromRight $ parse tokenize g
>             ty = opType (B0 :< ("a",0),0) op
>             r = evalStateT (elimWrap goal ctxt op ty) emptyContext
>         in do
>           putStrLn $ "\n" ++ show tm
>           case r of
>            Left ss -> do
>                 putStrLn $ "Error: " ++ intercalate "\n" ss
>            Right pfstate -> do
>                 putStrLn "Success."
>                 putStrLn pfstate)
>     testElimTerms
>         where elimWrap goal globalHyps op opType = do
>                   -- Make the eliminator
>                   elimTy <- bquoteHere opType
>                   make $ "elim" :<: elimTy
>                   goIn
>                   -- Introduce the arguments and give the applied elim/op-erator
>                   (t :=>: _) <- getGoal "testElimTerms"
>                   eHyps <- many $ lambdaBoy "elim"
>                   e <- give $ N (op :@ (map (\x -> N (P x))  eHyps))
>
>                   -- Make the goal
>                   make $ "goal" :<: goal
>                   goIn
>                   -- Introduce the external hypotheses
>                   extHyps <- sequence $ map (const $ lambdaBoy "extCtxt") globalHyps
>
>                   -- We have e an eliminator ready to fire
>                   -- We have a goal with internal hypotheses + goal
>                   elim (t :>: e)
>                   prettyProofState
