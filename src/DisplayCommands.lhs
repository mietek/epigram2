\section{Display Commands}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module DisplayCommands where

> import DisplayTm
> import Distiller
> import Elaborator
> import MissingLibrary
> import Naming
> import PrettyPrint
> import ProofState
> import Rooty
> import Rules
> import Tm

%endif


The |infoElaborate| command calls |elabInfer| on the given neutral display term,
evaluates the resulting term, bquotes it and returns a pretty-printed string
representation. Note that it works in its own module which it discards at the
end, so it will not leave any subgoals lying around in the proof state.

> infoElaborate :: INDTM -> ProofState String
> infoElaborate (DN tm) = do
>     makeModule "__infoElaborate"
>     goIn
>     ty :>: tm' <- elabInfer tm
>     tm'' <- bquoteHere (evTm (N tm'))
>     s <- prettyHere (ty :>: tm'')
>     goOut
>     dropModule
>     return s
> infoElaborate _ = throwError' "infoElaborate: can only elaborate neutral terms."


The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: INDTM -> ProofState String
> infoInfer (DN tm) = do
>     makeModule "__infoInfer"
>     goIn
>     ty :>: _ <- elabInfer tm
>     ty' <- bquoteHere ty
>     s <- prettyHere (SET :>: ty')
>     goOut
>     dropModule
>     return s
> infoInfer _ = throwError' "infoInfer: can only infer the type of neutral terms."


The |christenHere| command christens a term in the current context.

> christenHere :: INDTM -> ProofState (InDTm String)
> christenHere dtm = do
>     aus <- getAuncles
>     me <- getMotherName
>     return (christen aus me dtm)


The |prettyHere| command distills and christens a term in the current
context, then passes it to the pretty-printer.

> prettyHere :: (TY :>: INTM) -> ProofState String
> prettyHere tt = do
>     dtm :=>: _ <- distill tt
>     dtms <- christenHere dtm
>     return (show (pretty dtms))