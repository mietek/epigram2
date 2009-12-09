> module Tests.Lexer where
>             
> import Parsley       
> import Lexer

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
>         , "[| fancy |]"               -- empty fancy brackets
>         , "[foo| bar |foo]"           -- non-empty fancy brackets
>         ]

> main = 
>     sequence_ $
>     map (\t -> putStrLn $ show $ parse tokenize t) tests

