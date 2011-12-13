<         (p' :=>: p, True) <- runElabHope False
<             (PRF (EQBLUE (SET :>: LABEL m u) (SET :>: LABEL l ty)))

<         True <- withNSupply $ equal (SET :>: (u, ty))
<         (p' :=>: p, True) <- runElabHope False
<            (PRF (EQBLUE (u :>: m) (ty :>: l)))


>         m'   <- bquoteHere m
>         u'   <- bquoteHere u


<         return (N (coe :@ [LABEL m' u', LABEL l' ty', p', tm'])
<               :=>: coe @@ [LABEL m  u,  LABEL l  ty,  p,  tm], True)

<         return (N (coe :@ [LABEL m' u', LABEL l' ty', CON (PAIR (N (p' :? PRF (EQBLUE (u' :>: m') (ty' :>: l')) :$ Out)) (N (P refl :$ A SET :$ A u'))), tm'])
<              :=>: coe @@ [LABEL m  u,  LABEL l  ty,  CON (PAIR (p $$ Out) (NP refl $$ A SET $$ A u)),  tm], True)
