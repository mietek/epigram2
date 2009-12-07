This needs pretty much a total rewrite to match the new syntax of developments.


> data CoreLine
>   = LLam [String] (Maybe INTM)
>   | LDef String (Maybe INTM) [[Token]]
>   | LEq (Maybe INTM) (Maybe INTM)
>   | LCom
>   deriving Show

> pCoreLine :: Bwd Entry -> Parsley Token CoreLine
> pCoreLine es =
>   (|LLam (%keyword "\\"%) (some ident) (optional (termParse es))
>    |LCom (%keyword "--"; pRest%)

%if false

> -- FIX (or not):  |LDef ident (optional (keyword ":" >> pINTM es)) (keyword "where" *> pRest)

%endif

>    |LEq (%keyword "="%) (|Nothing (%keyword "?"%) | Just (termParse es)|)
>         (optional (keyword ":" >> termParse es))
>    |LCom (% many (keyword ";") %)
>    |)


The |coreLineAction| function takes a context, a |CoreLine| and a current
development. It attempts to update the development with the information
from the |CoreLine|, producing |Nothing| if this fails.

> coreLineAction :: Bwd Entry -> CoreLine -> Dev -> Maybe Dev
> coreLineAction gs (LLam [] _) d = Just d
> coreLineAction gs (LLam (x : xs) mty) (es, tip, r) = do
>   (st :=>: s) <- tipDom mty tip r
>   let xr = name r x := DECL :<: s
>   let xe = E xr (x, snd r) (Boy LAMB) st
>   coreLineAction gs (LLam xs mty) (es :< xe, tipRan tip xr r, roos r)
> coreLineAction gs LCom d = Just d
> coreLineAction gs (LDef x (Just ty) tss) (es, t, r) =
>   let  gs' = gs <+> es
>        vy = evTm ty
>        (d@(ds, u, _), tss') =
>          runWriter (makeFun gs' (B0, Unknown (ty :=>: vy), room r x) tss)
>        xr = name r x := (case u of
>               Unknown _ -> HOLE
>               Defined b _ ->
>                 DEFN (evTm (parBind gs' ds b))) :<: vy
>        xe = E xr (x, snd r) (Girl LETG d) ty
>   in   Just (es :< xe, t, roos r)
> coreLineAction gs (LEq (Just t) Nothing) (es, Unknown (u :=>: y), r) = do
>   () <- check (y :>: t) r
>   Just (es, Defined t (u :=>: y), r)
> coreLineAction gs (LEq (Just t) (Just y)) (es, tip, r) = do
>   () <- check (SET :>: y) r
>   let vy = evTm y
>   () <- case tip of
>      Unknown (_ :=>: y') -> guard $ equal (SET :>: (vy, y')) r
>      _ -> (|()|)
>   () <- check (vy :>: t) r
>   Just (es, Defined t (y :=>: evTm y), r)
> coreLineAction gs (LEq Nothing Nothing) (es, Unknown y, r) =
>   Just (es, Unknown y, r)
> coreLineAction gs (LEq Nothing (Just y)) (es, tip, r) = do
>   () <- check (SET :>: y) r
>   let vy = evTm y
>   () <- case tip of
>      Unknown (_ :=>: y') -> guard $ equal (SET :>: (vy, y')) r
>      _ -> (|()|)
>   Just (es, Unknown (y :=>: evTm y), r)
> coreLineAction _ _ _ = Nothing


> tipDom :: Maybe INTM -> Tip -> Root -> Maybe (INTM :=>: TY)
> tipDom (Just s)  Module                      r = do
>   () <- check (SET :>: s) r
>   return (s :=>: evTm s)
> tipDom (Just s)  (Unknown (_ :=>: PI s' _))  r = do
>   () <- check (SET :>: s) r
>   let vs = evTm s
>   guard $ equal (SET :>: (vs, s')) r
>   return (s :=>: vs)
> tipDom Nothing   (Unknown (_ :=>: PI s _))   r = Just (bquote B0 s r :=>: s)
> tipDom _         _                           r = Nothing


The |tipRan| function applies the $\Pi$-type at the |Unknown| tip to the given
reference, and returns an |Unknown| tip with the resulting type. If the tip
is a |Module|, it is returned unchanged.

> tipRan :: Tip -> REF -> Root -> Tip
> tipRan (Unknown (ty :=>: PI _ t))  x r  = let tyv = t $$ A (pval x) in
>   Unknown (bquote B0 tyv r :=>: tyv)
> tipRan Module                      _ _  = Module


The |makeFun| function takes a context, a development produced so far and a list
of lists of tokens. It attempts to interpret each list of tokens to update the
development, and writes out an updated list of lists of tokens with those that
fail commented out.

> makeFun :: Bwd Entry -> Dev -> [[Token]] -> Writer [[Token]] Dev
> makeFun gs d [] = (|d|)
> makeFun gs d@(ls, _, r) (ts : tss) =
>   fromMaybe (tell [Keyword "--" : ts] >> makeFun gs d tss) $ do
>     c <- either (const Nothing) Just $ parse (pCoreLine (gs <+> ls)) ts
>     d <- coreLineAction gs c d
>     return (tell [ts] >> makeFun gs d tss)
>            


The |devLoad| function takes a |[[Token]]| as produced by |layout|, and converts it
to a |Module| development. It returns the |Dev| produced, and a
|[[Token]]| with any lines that fail to type-check commented out.

< devLoad :: [[Token]] -> (Dev, [[Token]])
< devLoad tss = error "DevLoad: Broken for political reasons. -- Pierre"
<   --runWriter (makeFun B0 (B0, Module, (B0, 0)) tss)