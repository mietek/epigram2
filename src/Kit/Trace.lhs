\section{Trace}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}

> module Kit.Trace where

> import Debug.Trace

%endif

Let us enumerate the different flavours of tracing available:

> data Trace =  ProofTrace 
>            |  SimpTrace 
>            |  ElimTrace 
>            |  SchedTrace
>            |  ElabTrace
>               deriving Show

We then can switch each one on or off individually:

> traceEnabled :: Trace -> Bool
> traceEnabled ProofTrace  = True
> traceEnabled SimpTrace   = False
> traceEnabled ElimTrace   = False
> traceEnabled SchedTrace  = False
> traceEnabled ElabTrace   = True

That's fairly trivial, yet I'm pretty sure this goddamn laziness won't
skip some traces (ML programmer speaking here).

> monadTrace :: Monad m => Trace -> String -> m ()
> monadTrace t s  | traceEnabled t  = do
>     () <- trace  ("[" ++ show t ++ "] " ++ s) $ return ()
>     return ()
>                 | otherwise       = return ()

Some handy aliases for the tracing function:

> proofTrace  = monadTrace ProofTrace
> simpTrace   = monadTrace SimpTrace
> elimTrace   = monadTrace ElimTrace
> schedTrace  = monadTrace SchedTrace
> elabTrace   = monadTrace ElabTrace