> prettyModule :: Entries -> Name -> Dev Bwd -> Doc
> prettyModule aus me (B0, _, _) = empty
> prettyModule aus me dev = prettyDev aus me dev

> prettyDev :: Entries -> Name -> Dev Bwd -> Doc
> prettyDev gaus me (B0, Module,  _) = text "[]"
> prettyDev gaus me (B0, t,       _) = text ":=" <+> prettyTip gaus me t
> prettyDev gaus me dev@(es, t, r) =
>     lbrack <+> prettyEntries es aus $$ rbrack 
>     <+> prettyTip aus me t
>   where
>     aus = gaus BwdFwd.<+> es
>
>     prettyEntries :: Entries -> Entries -> Doc
>
>     prettyEntries (es' :< E ref _ (Boy k) _) (aus' :< _) =
>         prettyEntries es' aus'
>         $$ prettyBKind k (prettyRef aus me r ref) 
> 

If enabled, this case will print the fully lifted definition and type
(as contained in the reference) for each girl, which may be helpful
for debugging.

<     prettyEntries (es' :< E ref _ (Girl LETG dev) _) (aus' :< _) = 
<         prettyEntries es' aus'
<         $$ sep [prettyRef aus me r ref,
<                 nest 2 (prettyDev aus' (refName ref) dev) <+> semi]
                                         
>     prettyEntries (es' :< e) (aus' :< _) = 
>         prettyEntries es' aus'
>         $$ sep [text (christenName aus me (entryName e)),
>                 nest 2 (prettyDev aus' (entryName e) (entryDev e)) <+> semi]
>
>     prettyEntries B0 _ = empty

> prettyRef :: Entries -> Name -> Root -> REF -> Doc
> prettyRef aus me root ref@(_ := k :<: ty) = text (christenREF aus me ref) <+> prettyRKind k 
>   <+> pretty (christen aus me (unelaborate (bquote B0 ty root))) ArgSize
>     where prettyRKind :: RKind -> Doc
>           prettyRKind DECL      = text ":"
>           prettyRKind (DEFN v)  = text ":=" <+> pretty (christen aus me (unelaborate (bquote B0 v root))) ArgSize
>               <+> text ":"
>           prettyRKind HOLE      = text ":= ? :"

> prettyTip :: Entries -> Name -> Tip -> Doc
> prettyTip aus me Module                     = empty
> prettyTip aus me (Unknown     (tv :=>: _))  = text "? :" <+> pretty (christen aus me (unelaborate tv)) ArgSize
> prettyTip aus me (Defined tm  (tv :=>: _))  = pretty (christen aus me (unelaborate tm)) ArgSize
>     <+> text ":" <+> pretty (christen aus me (unelaborate tv)) ArgSize
