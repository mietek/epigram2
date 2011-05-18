\section{OpDef}

Gadgets for building operators so that they will evaluate and compile
coherently. 


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables #-}

> module Compiler.OpDef where

> import Evidences.Tm
> import Evidences.Eval
> import Evidences.Operators

%endif


> data OpDef  =  Arg (VAL -> OpDef)     -- Any argument
>             |  ConArg (VAL -> OpDef)  -- An argument that needs to be canonical
>             |  Body OpBody

> data OpBody  =  OpCase OpBody [OpBody]
>              |  IsZero OpBody OpBody OpBody
>              |  Val VAL 
>              |  Dec VAL (VAL -> OpBody)

> makeOpRun :: String -> OpDef -> [VAL] -> Either NEU VAL
> makeOpRun name (Arg fn) (v:vs) = makeOpRun name (fn v) vs
> makeOpRun name (ConArg fn) (N t:vs) = Left t
> makeOpRun name (ConArg fn) (CON v:vs) = makeOpRun name (fn v) vs
> makeOpRun name (ConArg fn) (v:vs) = makeOpRun name (fn v) vs
> makeOpRun name (Body b) [] = makeOpBody b where
>     makeOpBody :: OpBody -> Either NEU VAL
>     makeOpBody (OpCase v vs) =
>         case makeOpBody v of
>           Right i@(C _) -> if (num i < length vs) then
>                                makeOpBody (vs!!num i)
>                               else error $ "Missing case in " ++ name ++ ": " ++ 
>                                            show i ++ ", " ++ show (length vs)
>           Right (N t) -> Left t
>           Left t -> Left t
>     makeOpBody (IsZero v z s) =
>         case makeOpBody v of
>           Right ZE -> makeOpBody z
>           Right (SU _) -> makeOpBody s
>           Right (N t) -> Left t
>           Left t -> Left t
>     makeOpBody (Val v) = Right v
>     makeOpBody (Dec (SU x) fn) = makeOpBody (fn x)

>     num :: VAL -> Int
>     num ZE = 0
>     num (SU k) = (num k) + 1

> makeOpRun name _ vs = error $ name ++ " stuck at " ++ show vs

Operator descriptionss currently need to go here, with a signature in
the .lhs-boot. 

The operator should also be added to OpCompile and OpGenerate. e.g.

< import -> OpCompile where
<     ("switch", [e, x, p, b]) -> App (Var "__switch") [Ignore, x, Ignore, b]

< import -> OpGenerate where
<     ("switch", switchTest) :

The the version to evaluate can be generated with 'makeOpRun':

<   switchOp = Op
<     { opName  = "switch"
<     , opArity = 4
<     , opTyTel = sOpTy
<     , opRun   = makeOpRun "switch" switchTest
<     , opSimp  = \_ _ -> empty
<     } where ...


The compiler decorates operator names with @__@ (to prevent name clashes).
Arguments which are not needed at run time should be replaced with 'Ignore'
so that the compiler can erase them.

This is obviously not the neatest way of doing this. It would be better if
all of this could be captured in the definition of Op.

> switchTest :: OpDef
> switchTest = 
>       ConArg (\arg -> ConArg (\n -> 
>       Arg (\p -> Arg (\ps ->
>          Body (IsZero (Val n) 
>            (Val (ps $$ Fst))
>            (Dec n (\k ->
>               Val (switchOp @@ [arg $$ Snd $$ Fst, 
>                                 k,
>                                 L $ "x" :. [.x.  p -$ [ SU (NV x) ] ],
>                                 ps $$ Snd]))))
>            ))))
