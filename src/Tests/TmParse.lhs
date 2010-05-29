> module  Tests.TmParse where

> import Data.Foldable

> import DisplayLang.Lexer
> import DisplayLang.Naming
> import DisplayLang.PrettyPrint
> import DisplayLang.TmParse


> import Kit.Parsley


> tests = [ "Set"                         -- Set
>         , "Prop"                      -- Prop
>         , "(x : Set) -> Set"              -- Function space
>         , "( x : Set) -> Set"             -- Function space
>         , "( x : Set ) -> Set"            -- Function space
>         , "( x : Set )( y : Prop) -> Set"    -- Function space
>         , "( x : Set ) ( y : Set) -> Prop"   -- Function space
>         , "Set -> Set"                    -- Function space (non dep)
>         , "Set -> Set -> Set"               -- Function space (non dep)
>         , "(Set -> Set) -> Set"             -- Function space (non dep)
>         , "\\ x -> Set"                 -- Lambda
>         , "\\ x y -> Set"               -- Lambda
>         , "\\ x y z -> Set"             -- Lambda
>         , "\\ x y -> \\ z -> Set"       -- Lambda
>         , "Sig ()"                        -- unit
>         , "Sig ( Set ; Prop)"                  -- sigma
>         , "Sig ( Set ; Sig ())"                 -- sigma
>         , "Sig ( Set ; )"                   -- sigma
>         , "Sig ( Set ; Prop ; Set )"             -- sigma
>         , "Sig ( Set :- Prop)"                 -- sigma
>         , "Sig ( Set :- Prop ; Set )"            -- sigma
>         , "Sig ( Set :- Prop :- Prop )"           -- sigma
>         , "Sig ( x : Set ; Prop)"              -- sigma
>         , "Sig ( x : Set ; y : Prop ; Set)"      -- sigma
>         , "Sig ( x : Set ; z : Sig () ; )"      -- sigma
>         , "Sig ( y : Set ; )"               -- sigma
>         , "Sig ( x : Set ; Prop ; z : Set ; )"   -- sigma
>         , "Sig ( x : Set :- Prop)"             -- sigma
>         , "Sig ( x : Set :- Prop ; y : Set ;)"   -- sigma
>         , "Sig ( x : Set :- Prop :- Prop )"       -- sigma
>         , ":- Prop"                      -- proposition
>         , ":- (Prop -> Prop)"               -- proposition
>         , "(: Set) Set"                     -- ExTm
>         , "(: Set) Set -> Set"              -- ExTm
>         , "con Set"                       -- Con
>         , "con (\\ x -> Set)"              -- Con
>         , "[]"                        -- Tuple
>         , "[ Set Prop ]"                   -- Tuple
>         , "[ Set Prop Set ]"                 -- Tuple
>         , "[ Set (Set -> Set) (Set -> Set -> Set) ]" -- Tuple
>         , "[ Set / Prop ]"                 -- Tuple
>         , "[ Prop Set / Prop]"                -- Tuple
>         , "Enum []"                        -- Enum
>         , "Enum ['x]"                       -- Enum
>         , "Enum ['x 'y]"                   -- Enum
>         , "Enum ['x 'y 'z / Set]"         -- Enum
>         , "(x : Set) => Set"              -- Forall
>         , "( x : Set) => Set"             -- Forall
>         , "( x : Set ) => Set"            -- Forall
>         , "( x : Set )( y : Prop) => Set"    -- Forall
>         , "( x : Set ) ( y : Set) => Prop"   -- Forall
>         , "Set && Prop"                    -- And
>         , "((x : Set) => Set) && Set"       -- And
>         , "TT && FF"                  -- And
>         , "FF && FF"                  -- And
>         , "TT"                        -- Trivial
>         , "FF"                        -- Absurd
>         , "(: Set) Set == (: Set) Set"        -- EqBlue
>         , "(: Set) (Set -> Set) == (: Set) Prop" -- EqBlue
>         , "x"                         -- Name
>         , "x^2"                       -- Name
>         , "xx^242"                    -- Name
>         , "xx^242.y^12"               -- Name
>         , "xx^242.y^12.z^1"           -- Name
>         , "x -> y"                    -- Name
>         , "x y"                       -- Application
>         , "x y z"                     -- Application
>         , "f Set Set"                     -- Application
>         , "(Set : Set) <-> (Set : Set)"       -- EqGreen
>         , "((Set -> Set) : Set) <-> (Prop : Set)"-- EqGreen
>         , "eqGreen(x , y , z)"        -- Operator
>         , "elimOp()"                  -- Operator
>         , "elimOp(x)"                 -- Operator
>         , "elimOp(x , y)"             -- Operator
>         , "Branches(x , y)"           -- Operator
>         , "0"                         -- Nat
>         , "1"                         -- Nat
>         , "2"                         -- Nat
>         , "0 + x"                     -- Nat
>         , "1 + x"                     -- Nat
>         , "2 + x"                     -- Nat
>         , "f 1"                       -- Nat
>         , "( Set )"                     -- grouping
>         , "((Set))"                     -- grouping
>         , "` x"                       -- tag
>         , "` xy"                      -- tag
>         , "`x"                        -- tag
>         , "`xyz"                      -- tag
>         , "?a"                       -- hole
>         , "(: ?a) ?b -> ?c"        -- more holes
>         , "Mu d"                      -- mu
>         , "(: nat -> nat -> nat) con con [(\\ r r y -> y) (\\ r -> con \\ h r y -> suc (h y))]"         -- no longer a performance bug
>         , "(: nat -> nat -> nat) (con (con ([(\\ r r y -> y) (\\ r -> con (\\ h r y -> (suc (h y))))])))" -- no longer a performance bug
>         , "(: nat -> nat -> nat) (con (con ([(\\ r r y -> y) (\\ r -> con (\\ h r y -> (suc (h y))))])))" -- no longer a performance bug
>         , "A -> B -> C"                -- mixed pi-type
>         , "(x : A) -> (y : B) -> C"    -- mixed pi-type
>         , "A -> (x : B) -> C"          -- mixed pi-type
>         , "A -> ((x : B) -> C)"        -- mixed pi-type
>         , "Pi Set h"                   -- neutral pi-type
>         , "All Set h"                  -- neutral forall
>         , "Sig Set h"                  -- neutral sigma
>         , "_"                          -- underscore
>         ]

> test :: (Pretty x, Show x) => Parsley Token x -> String -> IO ()
> test p x =
>   let (Right tox) = parse tokenize x in
>     case parse p tox of
>       Left err -> putStrLn ("[FAILED] " ++ x ++ "\t==>\t" ++ show tox ++ "\t==>\t" ++ show err)
>       Right tm -> putStrLn ("[PASSED] " ++ x ++ "\t==>\t" ++ renderHouseStyle (pretty tm maxBound))

> main = foldMap (test pDInTm) tests