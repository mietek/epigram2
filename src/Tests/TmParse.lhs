> module  Tests.TmParse where

> import Parsley
> import Lexer
> import TmParse

> tests = [ "*"                         -- Set
>         , "#"                         -- Prop
>         , "(x : *) -> *"              -- Function space
>         , "( x : *) -> *"             -- Function space
>         , "( x : * ) -> *"            -- Function space
>         , "( x : * )( y : #) -> *"    -- Function space
>         , "( x : * ) ( y : *) -> #"   -- Function space
>         , "* -> *"                    -- Function space (non dep)
>         , "* -> * -> *"               -- Function space (non dep)
>         , "(* -> *) -> *"             -- Function space (non dep)
>         , "\\ x -> *"                 -- Lambda
>         , "\\ x y -> *"               -- Lambda
>         , "\\ x y z -> *"             -- Lambda
>         , "\\ x y -> \\ z -> *"       -- Lambda
>         , "()"                        -- unit
>         , "( * ; #)"                  -- sigma
>         , "( * ; ())"                 -- sigma
>         , "( * ; )"                   -- sigma
>         , "( * ; # ; * )"             -- sigma
>         , "( * :- #)"                 -- sigma
>         , "( * :- # ; * )"            -- sigma
>         , "( * :- # :- # )"           -- sigma
>         , "( x : * ; #)"              -- sigma
>         , "( x : * ; y : # ; *)"      -- sigma
>         , "( x : * ; z : () ; )"      -- sigma
>         , "( y : * ; )"               -- sigma
>         , "( x : * ; # ; z : * ; )"   -- sigma
>         , "( x : * :- #)"             -- sigma
>         , "( x : * :- # ; y : * ;)"   -- sigma
>         , "( x : * :- # :- # )"       -- sigma
>         , ":- #"                      -- proposition
>         , ":- (# -> #)"               -- proposition
>         , "* : *"                     -- ExTm
>         , "(* : *)"                   -- ExTm
>         , "(* -> * : *)"              -- ExTm
>         , "@ *"                       -- Con
>         , "@(\\ x -> *)"              -- Con
>         , "[]"                        -- Tuple
>         , "[ * # ]"                   -- Tuple
>         , "[ * # * ]"                 -- Tuple
>         , "[ * (* -> *) (* -> * -> *) ]" -- Tuple
>         , "[ * / # ]"                 -- Tuple
>         , "[ # * / #]"                -- Tuple
>         , "{}"                        -- Enum
>         , "{x}"                       -- Enum
>         , "{x , y}"                   -- Enum
>         , "{x, y}"                    -- Enum
>         , "{x , y , z}"               -- Enum
>         , "{ x , y , z }"             -- Enum
>         , "{ x , y , z / * }"         -- Enum
>         , "{ x , y , z / {} }"        -- Enum
>         , "(x : *) => *"              -- Forall
>         , "( x : *) => *"             -- Forall
>         , "( x : * ) => *"            -- Forall
>         , "( x : * )( y : #) => *"    -- Forall
>         , "( x : * ) ( y : *) => #"   -- Forall
>         , "* && #"                    -- And
>         , "((x : *) => *) && *"       -- And
>         , "TT && FF"                  -- And
>         , "FF && FF"                  -- And
>         , "TT"                        -- Trivial
>         , "FF"                        -- Absurd
>         , "(* : *) == (* : *)"        -- EqBlue
>         , "((* -> *) : *) == (# : *)" -- EqBlue
>         , "* : *"                     -- Annotate
>         , "(* -> *) : *"              -- Annotate
>         , "x"                         -- Name
>         , "x^2"                       -- Name
>         , "xx^242"                    -- Name
>         , "xx^242.y^12"               -- Name
>         , "xx^242.y^12.z^1"           -- Name
>         , "x -> y"                    -- Name
>         , "x y"                       -- Application
>         , "x y z"                     -- Application
>         , "f * *"                     -- Application
>         , "(* : *) <-> (* : *)"       -- EqGreen
>         , "((* -> *) : *) <-> (# : *)"-- EqGreen
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
>         , "( * )"                     -- grouping
>         , "((*))"                     -- grouping
>         , "` x"                       -- tag
>         , "` xy"                      -- tag
>         , "`x"                        -- tag
>         , "`xyz"                      -- tag
>         , "? a"                       -- hole
>         , "(? a : ? b) -> ? c"        -- more holes
>         ]


> main = do
>     Prelude.sequence_ $
>            map (\x -> 
>                 let tokenX = parse tokenize x in
>                 let parseX = parse bigInTm (fromRight tokenX) in
>                 putStrLn (x ++ "\t==>\t" ++ show tokenX ++ "\t==>\t" ++ show parseX))
>            tests
>                where fromRight (Right x) = x
>                      fromRight (Left x) = error $ show x

