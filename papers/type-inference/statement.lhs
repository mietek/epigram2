\section{Judgment typeclass}

> class Judgment j where
>     type Output j
>     fiat :: j -> Contextual (Output j)
>     orthogonal :: Entry -> j -> Bool

> instance Judgment () where
>     type Output () = ()
>     fiat () = return ()
>     orthogonal _ _ = True

> instance (Judgment j, Judgment k) => Judgment (j, k) where
>     type Output (j, k) = (Output j, Output k)
>     fiat (j, k) = do
>         a  <- fiat j
>         b  <- fiat k
>         return (a, b)
>     orthogonal e (a, b) = orthogonal e a && orthogonal e b

> instance Applicative Contextual where
>     pure = return
>     (<*>) = ap

> instance (Judgment j, Judgment k) => Judgment (Either j k) where
>     type Output (Either j k) = Either (Output j) (Output k)
>     fiat (Left j) = pure Left <*> fiat j
>     fiat (Right k) = pure Right <*> fiat k
>     orthogonal e = either (orthogonal e) (orthogonal e)

> data Unify = Type :==: Type
> infix 1 :==:

> data Instantiate = Name :===: (Type, Suffix)
> infix 1 :===:

> instance Judgment Unify where
>     type Output Unify = ()
>     fiat (tau    :==:   upsilon) = unify tau upsilon
>     orthogonal (delta := _) (V alpha :==: V beta) =
>         alpha /= delta && beta /= delta
>     orthogonal e (tau0 :-> tau1 :==: upsilon0 :-> upsilon1) =
>         orthogonal e (tau0 :==: upsilon0) && orthogonal e (tau1 :==: upsilon1)
>     orthogonal e (V alpha :==: tau) = orthogonal e (alpha :===: (tau, F0))
>     orthogonal e (tau :==: V alpha) = orthogonal e (alpha :===: (tau, F0))

> instance Judgment Instantiate where
>     type Output Instantiate = ()
>     fiat (alpha  :===:  (upsilon, _Xi)) = solve alpha _Xi upsilon
>     orthogonal (delta := _) (alpha :===: (tau, _Xi)) = not (alpha == delta) &&
>         not (delta <? tau) && not (delta <? _Xi)
>     orthogonal _ (_ :===: _) = True

> data Specialise = Specialise Scheme

> instance Judgment Specialise where
>     type Output Specialise = Type
>     fiat (Specialise sigma) = specialise sigma
>     orthogonal _ _ = False

> data Infer = Infer Term

> instance Judgment Infer where
>     type Output Infer = Type
>     fiat (Infer t) = infer t
>     orthogonal _ _ = False



> class Judgment j => Topmost j where
>     topmost :: Entry -> j -> Contextual (Output j, Maybe Suffix)
>     topset :: Entry -> j -> Contextual (Maybe Suffix)
>     topset e j = snd <$> topmost e j

> instance Topmost Instantiate where
>   topmost e j = (\_Xi -> ((),_Xi)) <$> topset e j
>   topset (delta := mt) (alpha :===: (tau, _Xi)) =
>    let occurs = delta <? tau || delta <? _Xi in case
>     (delta == alpha,  occurs,  mt            ) of
>     (True,            True,    _             )  ->  lift Nothing
>     (True,            False,   Nothing       )  ->  replace (_Xi <+> (alpha ::= Just tau :> F0))
>     (True,            False,   Just upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  solve alpha (delta ::= mt :> _Xi) tau
>                                                 >>  replace F0
>     (False,           False,   _             )  ->  undefined
>   topset _ _ = undefined


> onTop' :: Topmost j => j -> Contextual (Output j)
> onTop' j = do
>     e <- popEntry
>     if orthogonal e j
>         then do
>             x <- onTop' j
>             modifyContext (:< e)
>             return x
>         else do
>             (x, m) <- topmost e j
>             case m of
>                 Just _Xi  -> modifyContext (<>< _Xi)
>                 Nothing   -> modifyContext (:< e)
>             return x