\section{Enum}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Enum where

%endif

> import -> CanConstructors where
>   EnumU  :: Can t
>   EnumT  :: t -> Can t
>   NilE   :: Can t
>   ConsE  :: t -> t -> Can t
>   Ze     :: Can t
>   Su     :: t -> Can t 

> import -> CanPats where
>   pattern ENUMU      = C EnumU 
>   pattern ENUMT e    = C (EnumT e) 
>   pattern NILE        = C NilE
>   pattern CONSE t e  = C (ConsE t e) 
>   pattern ZE         = C Ze
>   pattern SU n       = C (Su n)

> import -> CanCompile where
>   makeBody Ze = CTag 0
>   makeBody (Su x) = STag (makeBody x)

> import -> TraverseCan where
>   traverse f EnumU        = (|EnumU|)
>   traverse f (EnumT e)    = (|EnumT (f e)|)
>   traverse f NilE         = (|NilE|)
>   traverse f (ConsE t e)  = (|ConsE (f t) (f e)|)
>   traverse f Ze           = (|Ze|)
>   traverse f (Su n)       = (|Su (f n)|) 

> import -> CanTyRules where
>   canTy tc (Set :>: EnumU)    = Just EnumU
>   canTy tc (Set :>: EnumT e)  =
>     ENUMU `tc` e &\ \ e _ ->
>     Just $ EnumT e
>   canTy tc (EnumU :>: NilE)       = Just NilE
>   canTy tc (EnumU :>: ConsE t e)  =
>     UID `tc` t    &\ \ t _ ->
>     ENUMU `tc` e  &\ \ e _ ->
>     Just $ ConsE t e
>   canTy tc (EnumT (CONSE t e) :>: Ze)    = Just Ze 
>   canTy tc (EnumT (CONSE t e) :>: Su n)  =
>     ENUMT e `tc` n &\ \ n _ ->
>     Just $ Su n

> import -> OpCode where
>   branchesOp = Op 
>     { opName   = "Branches"
>     , opArity  = 2 
>     , opTy     = bOpTy
>     , opRun    = bOpRun
>     } where
>         bOpTy ev [e , p] = 
>           Just ([ENUMU :>: e , Arr (ENUMT (ev e)) SET :>: p] , SET)
>         bOpTy _ _ = Nothing
>         bOpRun :: [VAL] -> Either NEU VAL
>         bOpRun [NILE , p] = Right UNIT
>         bOpRun [CONSE t e' , p] = 
>           Right (TIMES (p $$ A ZE) 
>                 (branchesOp @@ [e' , L (H (B0 :< p) 
>                                  "" (N (V 1 :$ A ((C (Su (N (V 0))))))))]))
>         bOpRun [N e , _] = Left e 
>
>   switchOp = Op
>     { opName = "Switch"
>     , opArity = 4
>     , opTy = sOpTy
>     , opRun = sOpRun
>     } where
>         sOpTy ev [e , p , b, x] = 
>           Just ([ ENUMU :>: e 
>                 , Arr (ENUMT (ev e)) SET :>: p
>                 , branchesOp @@ [ev e , ev p] :>: b
>                 , ENUMT (ev e) :>: x] , (ev p) $$ A (ev x))
>         sOpRun :: [VAL] -> Either NEU VAL
>         sOpRun [CONSE t e' , p , ps , ZE] = Right $ ps $$ Fst
>         sOpRun [CONSE t e' , p , ps , SU n] = Right $
>           switchOp @@ [e' 
>                       , L (H (B0 :< p) "" (N (V 1 :$ A ((C (Su (N (V 0))))))))
>                       , ps $$ Snd
>                       , n ]
>         sOpRun [_ , _ , _ , N n] = Left n


> import -> Operators where
>   branchesOp :
>   switchOp :

> import -> OpCompile where
>     ("Branches", _) -> Ignore
>     ("Switch", [e, p, b, x]) -> App (Var "switch") [b, x]

