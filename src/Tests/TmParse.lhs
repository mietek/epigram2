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
>         , "( * )"                     -- grouping
>         , "((*))"                     -- grouping
>         ]


> main = do
>     Prelude.sequence_ $
>            map (\x -> 
>                 let tokenX = parse tokenize x in
>                 let parseX = parse bigTmIn (fromRight tokenX) in
>                 putStrLn (x ++ "\t==>\t" ++ show tokenX ++ "\t==>\t" ++ show parseX))
>            tests
>                where fromRight (Right x) = x
>                      fromRight (Left x) = error $ show x

