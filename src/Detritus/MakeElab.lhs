
The |eEnsure| instruction demands that a value should be equal to a canonical
value with the given shape. It returns a term and value with the required shape,
together with a proof that these equal the input.

> eEnsure :: INTM :=>: VAL -> (Can VAL :>: Can ()) -> Elab (INTM :=>: Can VAL, INTM :=>: VAL)
> eEnsure (tm :=>: C v) (ty :>: t) = case halfZip v t of
>     Nothing  -> throwError' $ err "eEnsure: halfZip failed!"
>     Just _   -> do
>         ty' :=>: _ <- eQuote (C ty)
>         return (tm :=>: v, N (P refl :$ A ty' :$ A tm)
>                                  :=>: pval refl $$ A (C ty) $$ A (C v))
> eEnsure (_ :=>: L _) _ = throwError' $ err "eEnsure: failed to match lambda!"
> eEnsure (_ :=>: nv) (ty :>: t) = do
>     vu <- unWrapElab $ canTy chev (ty :>: t)
>     let v = fmap valueOf vu
>     pp <- eHopeFor . PRF $ EQBLUE (C ty :>: nv) (C ty :>: C v)
>     return (C (fmap termOf vu) :=>: v, pp)
>  where
>    chev :: (TY :>: ()) -> WrapElab (INTM :=>: VAL)
>    chev (ty :>: ()) = WrapElab (eHopeFor ty)


>     handleArgs (tm :=>: tv :<: ty) (A a : as) = do
>         ty' :=>: _ <- eQuote ty
>         (cty :=>: ctyv, q :=>: qv) <- eEnsure (ty' :=>: ty) (Set :>: Pi () ())
>         handleArgs (coe :@ [ty', cty, q, N tm] :=>: coe @@ [ty, C ctyv, qv, tv] :<: C ctyv) (A a : as)


> newtype WrapElab x = WrapElab {unWrapElab :: Elab x}
>     deriving (Functor, Applicative, Alternative, Monad)

> instance (MonadError (StackError ())) WrapElab where
>     throwError e = WrapElab (throwError [err "WrapElab: cannot unwrap error."])
>     catchError _ _ = WrapElab (throwError [err "WrapElab: cannot catch error."])
