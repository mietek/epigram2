> prettyProofState :: ProofState String
> prettyProofState = do
>     me <- getMotherName
>     gaus <- getGreatAuncles
>     ls <- gets fst
>     dev <- getDev
>     case ls of
>         B0      -> return (show (prettyModule gaus me dev))
>         _ :< _  -> return (show (prettyDev gaus me dev))
