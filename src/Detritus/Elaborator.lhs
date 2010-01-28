
> elabbedV :: VAL -> ProofState (INTM :=>: VAL)
> elabbedV v = do
>   t <- bquoteHere v
>   return (t :=>: v)


\subsection{$\lambda$-lifting}

The |gimme| operator elaborates every definition in the proof state, thereby
ensuring it is fully $\lambda$-lifted. Starting from the root of the proof
state, it processes each node in turn, first processing any children, then
the node itself.

> gimme = much goOut >> processNode
>   where
>     processNode :: ProofState ()
>     processNode = do
>         optional (do
>             goIn
>             much goUp
>             processNode
>             much (goDown >> processNode)
>             goOut
>           )
>         regive
>
>     regive :: ProofState ()
>     regive = do
>         tip <- getDevTip
>         m <- getMother
>         case {- |trace ("regive " ++ show (motherName m)) $| -} tip of
>             Defined tm (tipTyTm :=>: tipTy) -> do
>                 putDevTip (Unknown (tipTyTm :=>: tipTy))
>                 (tm' :=>: tv) <- elaborate True (tipTy :>: tm)
>                 Unknown tt <- getDevTip
>                 putDevTip (Defined tm' tt)
>             _ -> return ()


\section{Elab Monad}

> data Elab x
>   = Bale x
>   | Cry
>   | Hope
>   | EDef String INTM (Elab INTM) (VAL -> Elab x)
>   | ELam String (VAL -> Elab x)
>   | EPi String INTM (VAL -> Elab x)

> instance Monad Elab where
>   return = Bale
>   Bale x        >>= k = k x
>   Cry           >>= k = Cry
>   Hope          >>= k = Hope
>   EDef x y d f  >>= k = EDef x y d ((k =<<) . f)
>   ELam x f      >>= k = ELam x ((k =<<) . f)
>   EPi x y f     >>= k = EPi x y ((k =<<) . f)
>
> instance Functor Elab where
>   fmap = ap . return
>
> instance Applicative Elab where
>   pure = return
>   (<*>) = ap