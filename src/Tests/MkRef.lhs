> module Tests.MkRef where

> import Tm
> import Rules
> import Root
> import Rooty
> import BwdFwd
> import Control.Monad.Error

> import Debug.Trace

> testMkRef op = inCheck (check (opTy :>: (N $ P r))) (B0 :< ("tactics",0),0)
>     where r = mkRef op
>           opTy = pity $ opTyTel op

> main = 
>     sequence_ $ 
>     map (putStrLn . show . testMkRef) operators