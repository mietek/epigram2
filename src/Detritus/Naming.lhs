
> resolve :: Entries -> InDTm RelName -> Either [String] INDTM
> resolve es tm = trace ("Resolving " ++ show tm ++ " gave " ++ show tm') $ tm'
>     where tm' = resolver es B0 %$ tm

> resolveEx :: Entries -> ExDTm RelName -> Either [String] EXDTM
> resolveEx es tm = (|unDN (resolve es (DN tm)) |)
>   where unDN (DN tm) = tm

The |resolver| function takes a context and a list of binder names, and
produces a mangle that, when applied, attempts to resolve the parameter
names in an |InDTmRN| to produce an |InDTm REF|, i.e.\ an INDTM.

> resolver :: Entries -> Bwd String -> DMangle (Either [String]) RelName REF
> resolver ps vs = DMang
>     {  dmangP  = \ x mes -> let y = findLocal ps vs x in trace ("dmangP " ++ showRelName x ++ " gave " ++ show (|y $::$ mes|)) $ (| y $::$ mes |)
>     ,  dmangV  = \ _ _ -> Left ["resolver: what's that index doing here?"]
>     ,  dmangB  = \ x -> resolver ps (vs :< x)
>     }


The |findLocal| function takes a context, a list of binder names and a relative
name to resolve. It first searches the binders for a |Rel| name, and
returns a de Brujin indexed variable if it is present. Otherwise, it calls
|findGlobal| to search the context.

> findLocal :: Entries -> Bwd String -> RelName -> Either [String] (REF, Spine {TT} REF)
> findLocal ps B0 [(y, Rel 0)]
>   | Just ref <- lookup y primitives = Right (ref, [])
>   | Just ref <- lookup y axioms     = Right (ref, [])
> findLocal ps B0 sos = findGlobal ps sos
> findLocal ps (xs :< x) [(y, Rel 0)]       | x == y = Right (V 0, [])
> findLocal ps (xs :< x) ((y, Rel i) : sos) | x == y =
>   vinc <$> findLocal ps xs ((y, Rel (i - 1)) : sos)
> findLocal ps (xs :< x) sos = vinc <$> findLocal ps xs sos
>
> vinc :: EXTM -> EXTM
> vinc (V i)  = V (i + 1)
> vinc n      = n





The |christen| function takea a list of entries in scope (the auncles of the
current location), the name of the current location and a term. It replaces
the variables and parameters of the term with relative names as described
above, and removes common parameters.

> christen :: Entries -> Name -> INDTM -> InDTmRN
> christen es n tm = christener es n B0 %%$ tm


The business of christening is actually done by the following mangle, which
does most of its work in the |mangleP| function. 

> christener :: Entries -> Name -> Bwd String -> DMangle Identity REF RelName
> christener es me vs = DMang
>     {  dmangP = \(target := _) as -> pure (mangleP es me vs target (runIdentity as))
>     ,  dmangV = \i as -> (| (DP (vs !. i) $::$) as |)
>     ,  dmangB = \v -> christener es me (vs :< v)
>     }
