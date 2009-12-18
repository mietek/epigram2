%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Tests.CochonNat where

%endif

> import Control.Monad.State

> import Cochon
> import Developments
> import Elaborator
> import Nat
> import PrettyPrint
> import ProofState
> import Tm

> a = execStateT (do
>     make ("nat" :<: SET)
>     goIn
>     nat' <- bquoteHere nat
>     refNat <- elabGive nat'
>     
>     make ("two" :<: refNat)
>     goIn
>     two' <- bquoteHere two
>     give two'
>
>     make ("four" :<: refNat)
>     goIn
>     four' <- bquoteHere four
>     give four'
>
>     make ("plus" :<: ARR refNat (ARR refNat refNat))
>     goIn
>     plus' <- bquoteHere plus
>     give plus'
>   ) emptyContext 

> Right loc = a

> Right (s, _) = runStateT prettyProofState loc

> main = cochon loc

You might want to try

< make suc := (\ x -> @ [1 x]) : nat -> nat
< make f := @ @ [(\ r r y -> y) (\ r -> @ \ h r y -> suc (h y))] : nat -> nat -> nat
< make x := (f two two) : nat
< elab x
< compile x foo

and run the "foo" executable.