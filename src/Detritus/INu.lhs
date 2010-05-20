\section{INu}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.INu where

%endif

> import -> CanConstructors where
>   INu :: t -> t -> t -> Can t
>   ICoIt :: t -> t -> t -> t -> t -> t -> Can t

> import -> CanTraverse where
>   traverse f (INu ity d i) = (|INu (f ity) (f d) (f i)|)
>   traverse f (ICoIt ity d i sty g s) = 
>     (|ICoIt (f ity) (f d) (f i) (f sty) (f g) (f s)|)

> import -> CanHalfZip where
>   halfZip (INu ity0 d0 i0) (INu ity1 d1 i1)  = 
>     Just (INu (ity0,ity1) (i0,i1) (d0,d1))
>   halfZip (ICoIt ity0 d0 i0 sty0 g0 s0) (ICoIt ity1 d1 i1 sty1 g1 s1) = 
>     Just (ICoIt (ity0,ity1) (d0,d1) (i0,i1) (sty0,sty1) (g0,g1) (s0,s1))

> import -> CanPats where
>   pattern INU ity d i = C (INu ity d i)
>   pattern ICOIT ity d i sty f s = C (ICoIt ity d i sty f s)

> import -> CanDisplayPats where
>   pattern DINU ity d i = DC (INu ity d i)
>   pattern DICOIT ity d i sty f s = DC (ICoIt ity d i sty f s)

> import -> CanPretty where
>   pretty (INu ity d i)  = wrapDoc
>       (kword KwINu <+> pretty ity ArgSize <+> pretty d ArgSize
>            <+> pretty i ArgSize)
>       ArgSize
>   pretty (ICoIt ity d i sty f s) = wrapDoc
>       (kword KwICoIt <+>
>           pretty ity ArgSize <+> pretty d ArgSize <+> pretty i ArgSize <+>
>           pretty sty ArgSize <+> pretty f ArgSize <+> pretty s ArgSize)
>       ArgSize

> import -> CanTyRules where
>   canTy chev (Set :>: INu ity d i) = do
>     ityvv@(ity :=>: ityv) <- chev (SET :>: ity)
>     dvv   <- chev (ARR ityv (IDESC ityv) :>: d)
>     ivv   <- chev (ityv :>: i)
>     return $ INu ityvv dvv ivv
>   canTy chev (INu ity d i :>: Con t) =
>     (|Con (chev (idescOp @@ [ity
>                             ,d $$ A i
>                             ,L $ HF "S" $ \ sty -> INU ity d sty] :>: t))|)
>   canTy chev (INu ityv dv iv :>: ICoIt ity d i sty f s) = do
>     dvv <- chev (ARR ityv (IDESC ityv) :>: d)
>     ivv <- chev (ityv :>: i)
>     ityvv <- chev (SET :>: ity)
>     styvv@(sty :=>: styv) <- chev (ARR ityv SET :>: sty)
>     fvv@(f :=>: fv) <- chev (PI ityv (L $ HF "i" $ \i ->
>       ARR (styv $$ A i) (idescOp @@ [ityv,dv $$ A i,styv])) :>: f)
>     svv <- chev (styv $$ A iv :>: s)
>     return (ICoIt ityvv dvv ivv styvv fvv svv)

> import -> CanCompile where
>   makeBody (INu ity d i) = Ignore
>   makeBody (ICoIt ity d i sty f s) = 
>     App (Var "__icoit") (map makeBody [d,i,f,s])

> import -> ElimTyRules where
>   elimTy chev (_ :<: INu ity d iv) Out = 
>     return (Out, idescOp @@ [ity
>                             ,d $$ A iv
>                             ,L $ HF "i" $ \i -> INU ity d i])

> import -> ElimComputation where
>   ICOIT ity d i sty f s $$ Out = 
>     imapOp @@ [ity
>               ,d $$ A i
>               ,sty
>               ,L . HF "i" $ \i -> INU ity d i
>               ,L . HF "s" $ \s -> ICOIT ity d i sty f s
>               ,f $$ A i $$ A s]


> import -> KeywordConstructors where
>   KwINu    :: Keyword
>   KwICoIt  :: Keyword

> import -> KeywordTable where
>   key KwINu       = "INu"
>   key KwICoIt     = "ICoIt"

> import -> InDTmParsersSpecial where
>   (AndSize, (|DINU (%keyword KwINu%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|(DICOIT DU) (%keyword KwICoIt%)
>       (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)
>       (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
