\section{Resolving and unresolving names}
\label{sec:ProofState.Interface.NameResolution}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, PatternGuards #-}

> module ProofState.Interface.NameResolution where

> import Control.Applicative
> import Control.Monad.State
> import Data.Foldable hiding (elem, find)
> import Data.List
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import ProofState.Edition.ProofContext
> import ProofState.Edition.Entries
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState

> import DisplayLang.Name
> import DisplayLang.Scheme

> import Evidences.Tm
> import Evidences.Operators

%endif

\newcommand{\relname}[1]{\textit{#1}}

Typographical note: in this section, we write \relname{f} for a relative name 
(component) and @f_0@ for an absolute name (component).

A |BScopeContext| contains information from the |ProofContext|
required for name resolution: a list of the above entries and last
component of the current entry's name for each layer, along with the
entries in the current development.

> type BScopeContext =  (Bwd (Entries, (String, Int)), Entries) 

We can extract such a thing from a |ProofContext| using |inBScope|:

> inBScope :: ProofContext -> BScopeContext
> inBScope (PC layers dev _) = 
>   (  fmap (\l -> (aboveEntries l, last . currentEntryName . currentEntry $ l)) layers
>   ,  devEntries dev)

An |FScopeContext| is the forwards variant:

> type FScopeContext =  ( Fwd (Entry Bwd)
>                       , Fwd ((String, Int), Fwd (Entry Bwd))) 

We can reverse the former to produce the latter:

> bToF :: BScopeContext -> FScopeContext
> bToF (uess :< (es,u),es') = 
>     let (fs, vfss) = bToF (uess,es) in 
>     (fs, (u,es' <>> F0) :> vfss)
> bToF (B0,es) = (es <>> F0,F0) 


The |flat| function, up to currying, takes a |BScopeContext| and flattens it
to produce a list of entries.

> flat :: Bwd (Entries, (String,Int)) -> Entries -> Entries
> flat B0 es = es
> flat (esus :< (es',_)) es = flat esus (es' <+> es)

The |flatNom| function produces a name by prepending its second argument with
the name components from the backwards list. 

> flatNom :: Bwd (Entries, (String,Int)) -> Name -> Name
> flatNom B0 nom = nom
> flatNom (esus :< (_,u)) nom = flatNom esus (u : nom)


\subsection{Resolving relative names to references}

We need to resolve local longnames as references. We resolve \relname{f.x.y.z}
by searching outwards for \relname{f}, then inwards for a child \relname{x},
\relname{x}'s child \relname{y}, \relname{y}'s child \relname{z}. References are
fully $\lambda$-lifted, but as \relname{f}'s parameters are held in common with
the point of reference, we automatically supply them.


When in the process of resolving a relative name, we keep track of a
|ResolveState|. \question{What do the components mean?}

> type ResolveState =  (  Either FScopeContext Entries
>                      ,  [REF]
>                      ,  Maybe REF 
>                      ,  Maybe (Scheme INTM)
>                      )

The outcome of the process is a |ResolveResult|: a reference, a list of shared
parameters to which it should be applied, and a scheme for it (if there is one).

> type ResolveResult = (REF, [REF], Maybe (Scheme INTM))


The |resolveHere| command resolves a relative name to a reference,
a spine of shared parameters to which it should be applied, and
possibly a scheme. If the name ends with "./", the scheme will be
discarded, so all parameters can be provided explicitly.
\question{What should the syntax be for this, and where should it be handled?}

> resolveHere :: RelName -> ProofState ResolveResult
> resolveHere x = do
>     let (x', b) = shouldDiscardScheme x
>     uess <- gets inBScope
>     (r, s, ms) <- resolve x' uess 
>        `catchEither` (err $ "resolveHere: cannot resolve name: "
>                             ++ showRelName x')
>     return (r, s, if b then Nothing else ms)
>   where
>     shouldDiscardScheme :: RelName -> (RelName, Bool)
>     shouldDiscardScheme x =  if fst (last x) == "/"
>                              then  (init x,  True)
>                              else  (x,       False)

The |resolveDiscard| command resolves a relative name to a reference,
discarding any shared parameters it should be applied to.

> resolveDiscard :: RelName -> ProofState REF
> resolveDiscard x = resolveHere x >>= (\ (r, _, _) -> return r)


There are four stages relating to whether we are looking up or down
(\relname{\^} or \relname{\_})
and whether or nor we are navigating the part of the proof state which is on the
way back to (or from) the root of the tree to the cursor position.

We start off in |resolve|, which calls |lookUp| (for \relname{\^}) or |lookDown| 
(for \relname{\_}) to find the first name element. Then |lookFor| and |lookFor'|
recursively call each other and |lookDown| until we find the target name, in
which case we stop, or we reach the local part of the context, in which case
|lookLocal| is called. Finally, |lookLocal| calls |huntLocal| with an appropriate
list of entries, so it looks up or down until it finds the target name.

The |resolve| function starts the name resolution process: if the name is a
primitive we are done, otherwise it invokes |lookUp| or |lookDown| as appropriate
then continues with |lookFor|.

> resolve :: RelName -> BScopeContext -> Either (StackError t) ResolveResult
> resolve [(y, Rel 0)] _
>   | Just ref <- lookup y primitives  = Right (ref, [], Nothing)
> resolve ((x, Rel i) : us)  bsc = lookUp (x, i) bsc (bToF bsc)   >>= lookFor us
> resolve ((x, Abs i) : us)  bsc = lookDown (x, i) (bToF bsc) []  >>= lookFor us
> resolve []                 bsc = Left [err "Oh no, the empty name"]


> lookFor :: RelName -> ResolveState -> Either (StackError t) ResolveResult
> lookFor [] (_,         sp, Just r,   ms)  = Right (r, sp, ms) 
> lookFor [] (Left fsc,  sp, Nothing,  _)   = Left [err "Direct ancestors are not in scope!"]
> lookFor us (Left fsc,  sp, _,        _)   = do 
>     (x, _, z) <- lookFor' us fsc
>     return (x, sp, z)
> lookFor us (Right es, sp, mr, ms)         = lookLocal us es sp mr ms


> lookFor' :: RelName -> FScopeContext -> Either (StackError t) ResolveResult
> lookFor' ((x, Abs i) : us)  fsc = lookDown (x, i) fsc []  >>= lookFor us
> lookFor' ((x, Rel 0) : us)  fsc = lookDown (x, 0) fsc []  >>= lookFor us
> lookFor' ((x, Rel i) : us)  fsc = Left [err "Yeah, good luck with that"]
> lookFor' []                 fsc = Left [err "Oh no, the empty name"]


> lookUp :: (String, Int) -> BScopeContext -> FScopeContext -> 
>               Either (StackError t) ResolveState
> lookUp (x,i) (B0, B0) fs = Left [err $ "Not in scope " ++ x]
> lookUp (x,i) ((esus :< (es,(y,j))),B0) (fs,vfss) | x == y = 
>   if i == 0 then Right (Left (fs,vfss), paramREFs (flat esus es), Nothing, Nothing)
>             else lookUp (x,i-1) (esus,es) (F0,((y,j),fs) :> vfss)
> lookUp (x,i) ((esus :< (es,(y,j))),B0) (fs,vfss) = 
>   lookUp (x,i) (esus,es) (F0,((y,j),fs) :> vfss)
> lookUp (x,i) (esus, es :< e@(EModule n (Dev {devEntries=es'}))) (fs,vfss) | lastNom n == x =
>   if i == 0 then Right (Right es', paramREFs (flat esus es), Nothing, Nothing)
>             else lookUp (x,i-1) (esus,es) (e:>fs,vfss)
> lookUp (x,i) (esus, es :< e@(EDEF r (y,j) dkind (Dev {devEntries=es'}) _ _)) (fs,vfss) | x == y =
>   if i == 0 then Right (Right es', paramREFs (flat esus es), Just r, entryScheme e)
>             else lookUp (x,i-1) (esus,es) (e:>fs,vfss)
> lookUp (x,i) (esus, es :< e@(EPARAM r (y,j) _ _ _)) (fs,vfss) | x == y =
>   if i == 0 then Right (Right B0, [], Just r, Nothing)
>             else lookUp (x,i-1) (esus,es) (e:>fs,vfss)
> lookUp u (esus, es :< e) (fs,vfss) = lookUp u (esus,es) (e:>fs,vfss)


> lookDown :: (String,Int) -> FScopeContext -> [REF] -> 
>                 Either (StackError t) ResolveState

> lookDown (x, i) (e :> es, uess) sp =
>     if x == (fst $ entryLastName e)
>     then if i == 0
>          then case (|devEntries (entryDev e)|) of
>              Just zs  -> Right (Right zs, sp, entryRef e, entryScheme e)
>              Nothing  -> Right (Right B0, [], entryRef e, entryScheme e) 
>          else lookDown (x, i-1) (es, uess) (pushSpine e sp)
>     else lookDown (x, i) (es, uess) (pushSpine e sp)
>   where
>     pushSpine :: Entry Bwd -> [REF] -> [REF]
>     pushSpine (EPARAM r _ _ _ _) sp   = r : sp
>     pushSpine _ sp                   = sp

> lookDown (x, i) (F0 , (((y, j), es) :> uess)) sp =
>     if x == y
>     then if i == 0
>          then Right (Left (es, uess), sp, Nothing, Nothing)
>          else lookDown (x, i-1) (es, uess) sp
>     else lookDown (x, i) (es, uess) sp 

> lookDown (x, i) (F0, F0) fs = Left [err $ "Not in scope " ++ x]


> lookLocal :: RelName -> Entries -> [REF] -> Maybe REF -> Maybe (Scheme INTM) ->
>                  Either (StackError t) ResolveResult
> lookLocal ((x, Rel i) : ys) es sp _ _  = huntLocal (x, i) ys (reverse $ trail es) sp
> lookLocal ((x, Abs i) : ys) es sp _ _  = huntLocal (x, i) ys (trail es) sp
> lookLocal [] _ sp  (Just r)  ms        = Right (r, sp, ms)
> lookLocal [] _ _   Nothing   _         = Left [err "Modules have no term representation"]


> huntLocal :: (String, Int) -> RelName -> [Entry Bwd] -> [REF] ->
>                      Either (StackError t) ResolveResult
> huntLocal (x, i) ys (e : es) as =
>     if x == (fst $ entryLastName e)
>     then if i == 0
>          then case (|devEntries (entryDev e)|) of
>              Just zs  -> lookLocal ys zs as (entryRef e) (entryScheme e)
>              Nothing  -> Left [err "Params in other Devs are not in scope"] 
>          else huntLocal (x, i-1) ys es as
>     else huntLocal (x, i) ys es as 
> huntLocal (x, i) ys [] as = Left [err $ "Had to give up looking for " ++ x]




\subsection{Unresolving absolute names to relative names}
\label{subsec:ProofState.Interface.NameResolution.christening}

Just as resolution automatically supplies parameters to references
which are actually lifted, so its inverse, \emph{christening}, must
hide parameters to lifted references which can be seen locally. For
example, here

\begin{verbatim}
f [
  x : S
  g => t : T
  ] => g : T
\end{verbatim}

@g@ is actually represented as @f.g f.x@, but should be displayed as, er,
\relname{g}.

\subsubsection{In more detail}

Our job is to take a machine name and print as little of it a possible, while at 
the same time, turning the IANAN representation into a more human friendly, 
(hah!) relative offset form. Consider:

\begin{verbatim}
X [ \ a : A
   f [ \ b : B ->
       g [ ] => ? : T
     -= We are here =-
     ] => ? : S
   ] 
\end{verbatim}

How should we print the computer name @X_0.f_0.g_0@ ? A first
approximation would be \relname{g} since this is the bit that differs
from the name of the development we are in (@X_0.f_0@). And, indeed we
will always have to print this bit of the name. But there's more to
it, here we are assuming that we are applying @g@ to the same spine of
parameters as the parameters we are currently working under, which
isn't always true. We need to be able to refer to, for instance,
\relname{f.g}, which would have type |(b : B) -> T|. So we must really
resolve names with their spines compared to the current name and
parameters spine. So:

\begin{itemize}
\item @X_0.f_0.g_0 a b@ resoves to \relname{g}
\item @X_0.f_0.g_0 a@ resolves to \relname{f.g}
\item @X_0.f_0.g_0 a c@ resolves to \relname{f.g c}
\item @X_0.f_0.g_0@ resoves to \relname{X.f.g}
\end{itemize}

The job of naming boils down to unwinding the current name and spine until 
both are a prefix of the name we want to print, and its spine. We then print 
the suffix of the name applied to the suffix of the spine. So, far, so simple, 
but there are complications:

\paragraph{1) The current development is, kind of, in scope}

\begin{verbatim}
X [ \ a : A
   f [] => ? : U
   f [ \ b : B ->
       g [ ] => ? : T
     -= We are here =-
     ] => ? : S
   ]
\end{verbatim}

We never want the current development to be in scope, but with this naming 
scheme, we need to be very careful since \relname{f.g} is a valid name. Thus we
must  call @X_0.f_0@ by the name \relname{f\^1} even though @X_0.f_1@ is not in
scope.

\paragraph{2) Counting back to the top}

When we start looking for the first part of the name we need to print, we can't 
possibly know what it is, so we can't count how many times it is shadowed 
(without writing a circular program) This requires us to make two passes through 
the proof state. If we name @X_0.f_0 a@ in the 2nd example above, we must 1st 
work out the first part of the name is \relname{f} and then go back out work out
how many \relname{f}'s we jump over to get there. 

\paragraph{3) Counting down from the top}

Consider naming @X_0.f_1.g_0@ with no spine (again in the 2nd example dev) how 
do we render @f_1@. It's my contention that or reference point cannot be where 
the cursor is, since we've escaped that context, instead we should name it 
absolutely, counting down from @X@, so we should print \relname{X.f\_1.g}. Note
that \relname{f\_1} as a relative name component has a different meaning from
@f_1@ as an absolute name component, and in:

\begin{verbatim}
X [ \ a : A
   f [] => ? : U
   h [] => ? : V
   f [ \ b : B ->
       g [ ] => ? : T
     -= We are here =-
     ] => ? : S
   ]
\end{verbatim}

@X_0.f_2.g_0@ also resolves to \relname{X.f\_1.g}.

We can split the name into 3 parts:
\begin{itemize}
\item the section when the name differs from our current position;
\item the section where the name is the same but the spine is different; and
\item the section where both are the same.
\end{itemize}

We must only print the last part of the 1st, and we must print the 2nd 
absolutely. As far as I remember the naming of these three parts is dealt with 
by (respectively) |nomTop|, |nomAbs| and |nomRel|. 

\paragraph{4) Don't snap your spine}

Final problem! Consider this dev:

\begin{verbatim}
X [   
   f [ \ a : A -> 
       \ b : B ->
       g [ ] => ? : T
     -= We are here =-
     ] => ? : S
   ]
\end{verbatim}

How should we render @X_0.f_0.g_0 a@?. Clearly there is some sharing of the
spine with the current position, but we must still print \relname{f.g a} since
\relname{f.g} should have type |(a : A) (b : B) -> T|. Thus we must only compare
spines when we unwind a section from the name of the current development.


\subsubsection{Here goes...}

To |unresolve| an absolute name, we need its reference kind, the spine of
arguments to which it is applied, the context in which we are viewing it and
a list of entries in local scope. We obtain a relative name, the number of
shared parameters to drop, and the scheme of the name (if there is one).

> unresolve :: Name -> RKind -> Spine {TT} REF -> BScopeContext
>                   -> Entries -> (RelName, Int, Maybe (Scheme INTM))
> unresolve tar rk tas msc@(mesus, mes) les = 

We first check if the name refers to an element of the |primitives| list:

>     case find ((tar ==) . refName . snd) primitives of

If so, we return its short name with no shared parameters and no scheme.

>         Just (s, _)  -> ([(s, Rel 0)], 0, Nothing)

Otherwise, we actually have to do some work. We work in the |Maybe| monad and
|failNom| will be called if unresolution fails.

>         Nothing      -> maybe (failNom tar, 0, Nothing) id $
>             case (partNoms tar msc [] B0, rk) of

If the reference is a |DECL|, then it had better be a parameter above,
and we do not need to worry about shared parameters. We simply call
|nomTop| to find it.

>                 (_, DECL) ->  do
>                     (x, ms) <- nomTop tar (mesus, mes <+> les)
>                     return ([x], 0, ms)

>                 (Just (xs, Just (top, nom, sp, es)), _) -> do
>                     let  (top', nom', i, fsc) = matchUp (xs :<
>                                                   (top, nom, sp, (F0, F0))) tas
>                          mnom = take (length nom' - length nom) nom'
>                     (tn,  tms)  <- nomTop top' (mesus, mes <+> les)
>                     (an,  ams)  <- nomAbs mnom fsc
>                     (rn,  rms)  <- nomRel nom (es <+> les) Nothing 
>                     let ms = case  (null nom,  null mnom) of
>                                    (True,      True)   -> tms
>                                    (True,      False)  -> ams
>                                    (False,     _)      -> rms
>                     return ((tn : an) ++ rn, i, ms)

>                 (Just (xs, Nothing), FAKE) -> do
>                     let (top', nom', i, fsc) = matchUp xs tas 
>                     (tn, tms) <- nomTop top' (mesus, mes <+> les)
>                     (an, ams) <- nomAbs nom' fsc
>                     return ((tn : an), i, if null nom' then tms else ams)

If nothing else matches, we had better give up and go home.

>                 _ -> Nothing


\paragraph{Parting the noms}

\question{Does anyone know what this does?}

> partNoms :: Name -> BScopeContext -> Name 
>                  -> Bwd (Name, Name, Spine {TT} REF, FScopeContext)
>                  -> Maybe ( Bwd (Name, Name, Spine {TT} REF, FScopeContext) 
>                     , Maybe (Name,Name, Spine {TT} REF, Entries) ) 
> partNoms [] bsc _ xs = Just (xs, Nothing)
> partNoms nom@(top:rest) bsc n xs = case partNom n top bsc (F0,F0) of
>  Just (sp, Left es) -> Just (xs, Just (n ++ [top], rest, sp, es))
>  Just (sp, Right fsc) -> 
>    partNoms rest bsc (n ++ [top]) (xs:<(n ++ [top], rest, sp, fsc))
>  Nothing -> Nothing


> partNom :: Name -> (String, Int) -> BScopeContext -> FScopeContext
>                 -> Maybe (Spine {TT} REF, Either Entries FScopeContext)
> partNom hd top ((esus :< (es,top')), B0) fsc | hd ++ [top] == (flatNom esus []) ++ [top'] =
>   Just (paramSpine (flat esus es),Right fsc)
> partNom hd top ((esus :< (es,not)), B0) (js,vjss) =
>   partNom hd top (esus,es) (F0,(not,js):>vjss)
> partNom hd top (esus, es :< EModule n (Dev {devEntries=es'})) fsc | (hd ++ [top]) == n =
>   Just (paramSpine (flat esus es),Left es')
> partNom hd top (esus, es :< EDEF _ top' _ (Dev {devEntries=es'}) _ _) fsc | hd ++ [top] == (flatNom esus []) ++ [top'] =
>   Just (paramSpine (flat esus es),Left es')
> partNom hd top (esus, es :< e) (fs, vfss)  = partNom hd top (esus, es) (e:>fs,vfss)
> partNom _ _ _ _ = Nothing


\paragraph{Matching up}

If we have a backward list of gibberish and a spine, it is not hard to go
back until the spine from the gibberish is a prefix of the given spine,
then return the gibberish.

> matchUp :: Bwd (Name, Name, Spine {TT} REF, FScopeContext) 
>              -> Spine {TT} REF ->  (Name, Name, Int, FScopeContext)
> matchUp (xs :< (x, nom, sp, fsc)) tas
>     | sp `isPrefixOf` tas  = (x, nom, length sp, fsc)
> matchUp (xs :< _) tas      = matchUp xs tas


\paragraph{Different name}

First, |nomTop| handles the section where the name differs from our current
position. We call it by its |lastNom| but need to look up the offset and
scheme.

> nomTop :: Name -> BScopeContext -> Maybe ((String,Offs),Maybe (Scheme INTM))
> nomTop n bsc = do
>     (i, ms) <- countB 0 n bsc
>     return ((lastNom n, Rel i), ms)

To determine the relative offset, |nomTop| uses |countB|, which looks backwards
through the context, counting the number of things in scope with the same last
name component. This also returns the scheme attached, if there is one.

> countB :: Int -> Name -> BScopeContext -> Maybe (Int, Maybe (Scheme INTM))
> countB i n (esus :< (es', u'), B0)
>   | last n == u' && flatNom esus [] == init n  = (| (i, Nothing) |)
> countB i n (esus :< (es', u'), B0)
>   | lastNom n == fst u'                        = countB (i+1)  n (esus, es')
> countB i n (esus :< (es', u'), B0)             = countB i      n (esus, es')
>
> countB i n (esus, es :< EModule n' (Dev {devEntries=es'}))
>   | n == n'                                    = (| (i, Nothing) |)
> countB i n (esus, es :< EModule n' _)           
>   | lastNom n == lastNom n'                    = countB (i+1) n (esus, es)
> countB i n (esus, es :< e@(EEntity r u' _ _ _))
>   | last n == u' && refName r == n             = (| (i, entryScheme e) |)
> countB i n (esus, es :< EEntity _ u' _ _ _)
>   | lastNom n == fst u'                        = countB (i+1) n (esus, es)
>
> countB i n (esus, es :< _)                     = countB i n (esus, es)
>
> countB _ n _                                   = Nothing 



\paragraph{Same name, different spine}

Next, |nomAbs| handles the section where the name is the same as the current
location but the spine is different.

> nomAbs :: Name -> FScopeContext -> Maybe (RelName, Maybe (Scheme INTM))
> nomAbs [u] (es,(_,es'):>uess) = do
>   (v,ms) <- findF 0 u es
>   (| ([v],ms) |)
> nomAbs ((x,_):nom) (es,(_,es'):>uess) = do 
>   (nom',ms) <- nomAbs nom (es',uess)
>   case countF x es of
>     0 -> (| ((x,Rel 0) : nom', ms) |)
>     j -> (| ((x,Abs j) : nom', ms) |)
> nomAbs [] _ = Just ([], Nothing)
> nomAbs _ _ = Nothing

> countF :: String -> Fwd (Entry Bwd) -> Int
> countF x F0 = 0
> countF x (EModule n _ :> es) | (fst . last $ n) == x = 1 + countF x es
> countF x (EEntity _ (y,_) _ _ _ :> es) | y == x = 1 + countF x es
> countF x (_ :> es) = countF x es

> findF :: Int -> (String,Int) -> Fwd (Entry Bwd) 
>              -> Maybe ((String,Offs), Maybe (Scheme INTM))
> findF i u (EModule n _ :> es) | (last $ n) == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), Nothing)
> findF i u@(x,_) (EModule n _ :> es) | (fst . last $ n) == x = findF (i+1) u es
> findF i u (e@(EDEF _ v dkind _ _ _) :> es) | v == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), entryScheme e)
> findF i u (EEntity _ v _ _ _ :> es) | v == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), Nothing)
> findF i u@(x,_) (EEntity _ (y,_) _ _ _ :> es) | y == x = findF (i+1) u es
> findF i u (_ :> es) = findF i u es
> findF _ _ _ = Nothing


\paragraph{Same name and spine}

Finally, |nomRel| handles the section where the name and spine both match the
current location.

> nomRel :: Name -> Entries 
>                -> Maybe (Scheme INTM) -> Maybe (RelName, Maybe (Scheme INTM)) 
> nomRel [] _ ms = (| ([], ms) |)
> nomRel (x : nom) es _ = do
>   (i,es',ms) <- nomRel' 0 x es
>   (nom',ms') <- nomRel nom es' ms
>   return ((fst x,Rel i):nom',ms')

> nomRel' :: Int -> (String,Int) -> Entries 
>                -> Maybe (Int,Entries, Maybe (Scheme INTM))
> nomRel' o (x,i) (es:< EModule n (Dev {devEntries=es'})) | (fst . last $ n) == x  = 
>   if i == (snd . last $ n) then (| (o,es',Nothing) |) 
>                            else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:< e@(EDEF _ (y,j) dkind (Dev {devEntries=es'}) _ _)) | y == x =
>   if i == j then (| (o,es',entryScheme e) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:< EEntity _ (y,j) _ _ _) | y == x = 
>   if i == j then (| (o,B0,Nothing) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<e) = nomRel' o (x,i) es
> nomRel' _ _ _ = Nothing


\subsubsection{Useful oddments for unresolution}

The common |lastNom| function extracts the |String| component of the last part
of a name.

> lastNom :: Name -> String
> lastNom = fst . last


The |failNom| function is used to give up and convert an absolute name that
cannot be unresolved into a relative name. This can happen when distilling
erroneous terms, which may not be well-scoped.

> failNom :: Name -> RelName
> failNom nom = ("!!!",Rel 0):(map (\(a,b) -> (a,Abs b)) nom)


\subsubsection{Invoking unresolution}

The |christenName| and |christenREF| functions call |unresolve| for names, and
the name part of references, respectively.

> christenName :: BScopeContext -> Name -> RKind -> RelName
> christenName bsc target rk = s
>   where (s, _, _) = unresolve target rk (paramSpine . (uncurry flat) $ bsc) bsc B0
>
> christenREF :: BScopeContext -> REF -> RelName
> christenREF bsc (target := rk :<: _) = christenName bsc target rk


The |showEntries| function folds over a bunch of entries, christening
them with the given entries in scope and current name, and
intercalating to produce a comma-separated list.

> showEntries :: (Traversable f, Traversable g) => BScopeContext -> f (Entry g) -> String
> showEntries bsc = intercalate ", " . foldMap f
>   where
>     f e | Just r <- entryRef e  = [showRelName (christenREF bsc r)]
>         | otherwise             = []

The |showEntriesAbs| function works similarly, but uses absolute names instead of
christening them.

> showEntriesAbs :: Traversable f => f (Entry f) -> String
> showEntriesAbs = intercalate ", " . foldMap f
>   where
>     f e = [showName (entryName e)]



