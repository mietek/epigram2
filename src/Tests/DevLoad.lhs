> module  Tests.DevLoad where

> import Control.Monad.State
> import Data.List

> import BwdFwd
> import DevLoad
> import Elaborator
> import Parsley
> import PrettyPrint
> import ProofState
> import Lexer


> tests =  [ ""
>          , "[ f := * : * ; ]"  
>          , "[ S [ \\ X : * -> ] * : * ; T := (S *) : * ; ]"
>          , "[ f [ \\ x : * -> ] ? : (* -> *) [| lambda y ; give x |] ; ]"
>          , "make a : * ; out ; make f : a -> a ; lambda x ; give x"
>          , "[ a ^ 1 := ? : * ; a := ? : * ; ]"
>          , "[ f [ g := ? : * ; ] ? : * ; ]"
>          , "[ f [ \\ x : * -> g := * : * ; ] ? : * ; ]"
>          , "[ f [ \\ x : * -> g := ? : * ; g := g : * ; ] ? : * ; ]"
>          , "[ a [ ] ; ]"
>          , "[ a [ x := * : * ; ] ; ]"
>          ]


> main = do
>     Prelude.sequence_ $
>            map (\x -> 
>                 let  Right ts = parse tokenize x
>                      mps = execStateT (devLoad ts) emptyContext
>                 in putStrLn ("\n" ++ x ++ "\n" ++ show ts ++ "\n" ++ case mps of
>                     Left ss -> "Error: " ++ intercalate "\n" ss
>                     Right loc@(B0, dev) -> show (prettyModule (greatAuncles loc) [] dev)))
>            tests

