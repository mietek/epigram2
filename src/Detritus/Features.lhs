> import -> ElaborateRules where
>   elaborate top (PROP :>: DEqBlue t u) = do
>       ((ttm :=>: tv) :<: tty, _) <- elabInfer t
>       ((utm :=>: uv) :<: uty, _) <- elabInfer u
>       tty' <- bquoteHere tty
>       uty' <- bquoteHere uty
>       return ((EQBLUE (tty' :>: N ttm) (uty' :>: N utm))
>               :=>: (EQBLUE (tty :>: tv) (uty :>: uv)))