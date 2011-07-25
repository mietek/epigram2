\section{Resolving and unresolving names}
\label{sec:ProofState.NameResolution}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, PatternGuards #-}

> module ProofState.NameResolution where

> import Prelude hiding (compare, all)

> import Control.Applicative
> import Control.Monad.State
> import Data.Foldable hiding (elem, find)
> import Data.List hiding (all)
> import Data.Maybe
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.NatFinVec

> import ProofState.Structure
> import ProofState.ProofContext
> import ProofState.GetSet

> import DisplayLang.Name
> import DisplayLang.Scheme

> import Evidences.Tm
> import Evidences.Primitives
> import Evidences.ErrorHandling
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.TypeChecker

%endif




\newcommand{\relname}[1]{\textit{#1}}

Typographical note: in this section, we write \relname{f} for a relative name 
(component) and @f_0@ for an absolute name (component).

A |BScopeContext| contains information from the |ProofContext|
required for name resolution: a list of the above entries and last
component of the current entry's name for each layer, along with the
entries in the current development.

> type BScopeContext =  (Bwd (Entries, (String, Int), HypState), Entries) 

We can extract such a thing from a |ProofContext| using |inBScope|:

> inBScope :: ProofContext -> BScopeContext
> inBScope (PC layers dev _) = 
>   (  fmap (\l -> (  aboveEntries l
>                  ,  last . currentEntryName . currentEntry $ l
>                  ,  layHypState l 
>                  )) layers
>   ,  devEntries dev)

An |FScopeContext| is the forwards variant:

> type FScopeContext =  ( Fwd (Entry Bwd)
>                       , Fwd ((String, Int), HypState, Fwd (Entry Bwd))) 

We can reverse the former to produce the latter:

> bToF :: BScopeContext -> FScopeContext
> bToF (uess :< (es,u,hs),es') = 
>     let (fs, vfss) = bToF (uess,es) in 
>     (fs, (u,hs,es' <>> F0) :> vfss)
> bToF (B0,es) = (es <>> F0,F0) 


The |flat| function, up to currying, takes a |BScopeContext| and flattens it
to produce a list of entries.

> flat :: Bwd (Entries, (String,Int), HypState) -> Entries -> Entries
> flat B0 es = es
> flat (esus :< (es',_,_)) es = flat esus (es' <+> es)

The |flatNom| function produces a name by prepending its second argument with
the name components from the backwards list. 

> flatNom :: Bwd (Entries, (String,Int), HypState) -> Name -> Name
> flatNom B0 nom = nom
> flatNom (esus :< (_,u,_)) nom = flatNom esus (u : nom)

\subsection{Resolving relative names to references}

We need to resolve local longnames as references. We resolve \relname{f.x.y.z}
by searching outwards for \relname{f}, then inwards for a child \relname{x},
\relname{x}'s child \relname{y}, \relname{y}'s child \relname{z}. References are
fully $\lambda$-lifted, but as \relname{f}'s parameters are held in common with
the point of reference, we automatically supply them.


When in the process of resolving a relative name, we keep track of a
|ResolveState|. \question{What do the components mean?}

> type ResolveState =  (  Either FScopeContext Entries
>                      ,  Maybe Int
>                      ,  Maybe DEF 
>                      ,  Maybe Scheme
>                      )

The outcome of the process is a |ResolveResult|: a reference, a list of shared
parameters to which it should be applied, and a scheme for it (if there is one).

> type ResolveResult = Either (Int, String, TY) (DEF, Maybe Int, Maybe Scheme)

< type ResolveResult = (REF, [REF], Maybe (Scheme INTM))


The |resolveHere| command resolves a relative name to a reference,
a spine of shared parameters to which it should be applied, and
possibly a scheme. If the name ends with "./", the scheme will be
discarded, so all parameters can be provided explicitly.
\question{What should the syntax be for this, and where should it be handled?}

> resolveHere :: RelName -> ProofState (Tm {Body, Exp, n}, Int, Maybe Scheme)
> resolveHere x = do
>     let (x', b) = shouldDiscardScheme x
>     uess <- gets inBScope
>     l <- getDevLev
>     res <- resolve x' l uess 
>        `catchEither` (err $ "resolveHere: cannot resolve name: "
>                             ++ showRelName x')
>     case res of
>       Left (l, s, t) -> return $ (P (l, s, t) :$ B0 , 0, Nothing)
>       Right (d, Just i, m) -> return $ (D d :$ B0, i, if b then Nothing else m)
>       Right (d, Nothing, m) -> return $ (D d :$ B0, 0, if b then Nothing else m)

>   where
>     shouldDiscardScheme :: RelName -> (RelName, Bool)
>     shouldDiscardScheme x =  if fst (last x) == "/"
>                              then  (init x,  True)
>                              else  (x,       False)

The |resolveDiscard| command resolves a relative name to a reference,
discarding any shared parameters it should be applied to.

> resolveDiscard :: RelName -> ProofState DEF
> resolveDiscard x = resolveHere x >>= (\ (d, _, _) -> return (unD d))
>   where unD :: Tm {Body, Exp, n} -> DEF
>         unD (D d :$ B0) = d


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

> resolve :: RelName -> Int -> BScopeContext -> Either (StackError) ResolveResult

> resolve [(y, Rel 0)] l _
>   | Just def <- find (\ a -> defName a == [("PRIM",0),(y,0)]) prims 
>       = Right (Right (def, 0, Nothing))

> resolve ((x, Rel i) : us)  l bsc = do
>   x <- lookUp (x, i) (Just l) bsc (F0, F0)   
>   case x of
>     (Right y) -> lookFor us y
>     (Left z) -> Right (Left z)
> resolve ((x, Abs i) : us)  l bsc = lookDown (x, i) (bToF bsc) 0  >>= lookFor us
> resolve []                 l bsc = Left [err "Oh no, the empty name"]


> lookFor :: RelName -> ResolveState -> Either (StackError) ResolveResult
> lookFor [] (_,         l, Just r,   ms)  = Right (Right (r, l, ms))
> lookFor [] (Left fsc,  l, Nothing,  _)   = Left [err "Direct ancestors are not in scope!"]
> lookFor us (Left fsc,  l, _,        _)   = do 
>     res <- lookFor' us 0 fsc
>     case res of 
>       Right (x, Nothing, z) -> return $ Right (x, Nothing, z) 
>       Right (x, _, z) -> return $ Right (x, l, z) 
> lookFor us (Right es,  l, mr, ms)         = lookLocal us es l mr ms


> lookFor' :: RelName -> Int -> FScopeContext -> Either (StackError) ResolveResult
> lookFor' ((x, Abs i) : us)  l fsc = lookDown (x, i) fsc 0  >>= lookFor us
> lookFor' ((x, Rel 0) : us)  l fsc = lookDown (x, 0) fsc 0  >>= lookFor us
> lookFor' ((x, Rel i) : us)  l fsc = Left [err "Yeah, good luck with that"]
> lookFor' []                 l fsc = Left [err "Oh no, the empty name"]


> lookUp :: (String, Int) -> Maybe Int -> BScopeContext -> FScopeContext -> 
>               Either StackError (Either (Int, String, TY) ResolveState)
> lookUp (x,i) l (B0, B0) fs = Left [err $ "lookup: Not in scope " ++ x]
> lookUp (x,i) l ((esus :< (es,(y,j),hs)),B0) (fs,vfss) | x == y = 
>   if i == 0 then Right (Right (Left (fs,vfss), l, Nothing, Nothing))
>             else lookUp (x,i-1) (case hs of InheritHyps -> l
>                                             NixHyps -> Nothing)
>                         (esus,es) (F0,((y,j),hs,fs) :> vfss)
> lookUp (x,i) l ((esus :< (es,(y,j),hs)),B0) (fs,vfss) = 
>   lookUp (x,i) (case hs of InheritHyps -> l
>                            NixHyps -> Nothing) 
>                (esus,es) (F0,((y,j),hs,fs) :> vfss)
> lookUp (x,i) l (esus, es :< e@(EModule n (Dev {devHypState=hs, devEntries=es'}))) (fs,vfss) | lastNom n == x =
>   if i == 0 then Right (Right (Right es', case hs of InheritHyps -> l
>                                                      NixHyps -> Nothing
>                                         , Nothing, Nothing))
>             else lookUp (x,i-1) l (esus,es) (e:>fs,vfss)
> lookUp (x,i) l (esus, es :< e@(EDef d (Dev {devHypState=hs, devEntries=es'}) sch)) (fs,vfss) 
>     | x == (fst $ last $ defName d) =
>   if i == 0 then Right (Right (Right es', case hs of InheritHyps -> l 
>                                                      NixHyps -> Nothing
>                                         , Just d, sch))
>             else lookUp (x,i-1) l (esus,es) (e:>fs,vfss)
> lookUp (x,i) l (esus, es :< e@(EParam _ s t l')) (fs,vfss) | x == s =
>   if i == 0 then Right (Left (l', s, t))
>             else lookUp (x,i-1) (|l - ~1|) (esus,es) (e:>fs,vfss)
> lookUp (x,i) l (esus, es :< e@(EParam _ _ _ _)) (fs,vfss) =
>             lookUp (x,i) (|l - ~1|) (esus,es) (e:>fs,vfss)
> lookUp u l (esus, es :< e) (fs,vfss) = lookUp u l (esus,es) (e:>fs,vfss)


> lookDown :: (String,Int) -> FScopeContext -> Maybe Int -> 
>                 Either (StackError) ResolveState
> lookDown (x, 0) (EParam _ s _ _ :> es, uess) sp | x == s =
>   Left [err "lookDown Param"]
> lookDown (x, i) (e@(EParam _ s _ _) :> es, uess) sp | x == s =
>   lookDown (x, i-1) (es, uess) (pushSpine e sp)
> lookDown (x, i) (e@(EParam _ s _ _) :> es, uess) sp =
>   lookDown (x, i) (es, uess) (pushSpine e sp)
> lookDown (x, i) (e :> es, uess) sp =
>     if x == (fst $ last $ maybe (error "A") id $ entryName e)
>     then if i == 0
>          then 
>            let edev = entryDev e 
>            in case ((|devEntries edev|), (|devHypState edev|))  of
>              (Just zs, Just InheritHyps)  -> Right (Right zs, sp, entryDef e, entryScheme e)
>              (Just zs, Just NixHyps)  -> Right (Right zs, Nothing, entryDef e, entryScheme e)
>              _  -> Right (Right B0, Just 0,  entryDef e, entryScheme e) 
>          else lookDown (x, i-1) (es, uess) (pushSpine e sp)
>     else lookDown (x, i) (es, uess) (pushSpine e sp)
> lookDown (x, i) (F0 , (((y, j), hs, es) :> uess)) sp =
>     if x == y
>     then if i == 0
>          then Right (Left (es, uess), sp, Nothing, Nothing)
>          else lookDown (x, i-1) (es, uess) (case hs of InheritHyps -> sp
>                                                        NixHyps -> Nothing)
>     else lookDown (x, i) (es, uess) sp 

> lookDown (x, i) (F0, F0) fs = Left [err $ "Not in scope " ++ x]

> pushSpine :: Entry Bwd -> Maybe Int -> Maybe Int
> pushSpine (EParam _ _ _ _) sp   =  (| (+1) sp |)
> pushSpine _ sp                  =  sp



> lookLocal :: RelName -> Entries -> Maybe Int -> Maybe DEF -> Maybe Scheme ->
>                  Either (StackError) ResolveResult
> lookLocal ((x, Rel i) : ys) es sp _ _  = huntLocal (x, i) ys (reverse $ trail es) sp
> lookLocal ((x, Abs i) : ys) es sp _ _  = huntLocal (x, i) ys (trail es) sp
> lookLocal [] _ sp  (Just r)  ms        = Right (Right (r, sp, ms))
> lookLocal [] _ _   Nothing   _         = Left [err "Modules have no term representation"]


> huntLocal :: (String, Int) -> RelName -> [Entry Bwd] -> Maybe Int ->
>                      Either (StackError) ResolveResult
> huntLocal (x, 0) ys (EParam _ s _ _ : es) as | x == s =
>    Left [err "Params in other Devs are not in scope"] 
> huntLocal (x, i) ys (EParam _ s _ _ : es) as | x == s =
>    huntLocal (x, i-1) ys es as
> huntLocal (x, i) ys (EParam _ s _ _ : es) as =
>    huntLocal (x, i) ys es as 
> huntLocal (x, i) ys (e : es) as =
>     if x == (fst $ last $ maybe (error "B") id $ entryName e)
>     then if i == 0
>          then case ((|devEntries (entryDev e)|),(|devHypState (entryDev e)|)) of
>              (Just zs,Just InheritHyps)  -> lookLocal ys zs as (entryDef e) (entryScheme e)
>              (Just zs,Just NixHyps)  -> lookLocal ys zs Nothing (entryDef e) (entryScheme e)
>              _  -> Left [err "Params in other Devs are not in scope"] 
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

> unresolveP :: (Int, String, TY) -> Bwd (Int, String, TY) -> ProofState RelName
> unresolveP (l, s, t) ps = do
>   let les = fmap (\ (l, s, t) -> EParam ParamLam s t l) ps
>   (mesus, mes) <- gets inBScope
>   return $ maybe (failNom [(s,l)]) id $ findParam l s (mesus, mes <+> les) 0

> findParam :: Int -> String -> BScopeContext -> Int -> Maybe RelName
> findParam l s (esus :< (es', (s',_), _), B0) o | s == s' = 
>   findParam l s (esus, es') (o+1)
> findParam l s (esus :< (es', u', _), B0) o = 
>   findParam l s (esus, es') o
> findParam l s (esus, es :< EModule n _) o | s == lastNom n =
>   findParam l s (esus, es) (o+1)
> findParam l s (esus, es :< EDef d _ _) o | s == lastNom (defName d) =
>   findParam l s (esus, es) (o+1)
> findParam l s (esus, es :< EParam k s' t' l') o | l == l' = 
>   (| [(s',Rel o)] |)
> findParam l s (esus, es :< EParam k s' t' l') o | s == s' = 
>   findParam l s (esus, es) (o+1)
> findParam l s (esus, es :< _) o = findParam l s (esus, es) o
> findParam _ _ _ _ = Nothing


> unresolveD :: DEF -> Bwd (Int, String, TY) -> Bwd (Elim EXP) -> 
>               ProofState (RelName, Maybe TY, [ Elim EXP ], Maybe Scheme)
> unresolveD d ps sp 
>     | ("PRIM",0) == head (defName d) =
>   return $  (  map (\(a,b) -> (a, Rel 0)) $ tail (defName d)
>             ,  Just $ defTy d, trail sp, Nothing) 
> unresolveD d ps tsp = do
>   lev <- getDevLev
>   let les = fmap (\ (l, s, t) -> EParam ParamLam s t l) ps
>   (mesus, mes) <- gets inBScope
>   (nn , os , ns, ms) <- 
>       maybe (return (failNom (defName d), Nothing, trail tsp, Nothing)) return $
>     case partNoms (defName d) (mesus,mes) [] InheritHyps B0 of
>       (Just (NixHyps, _, Just (top, nom, sp, es))) -> do
>         (tn,  tms)  <- nomTop top (mesus, mes <+> les)
>         (rn,  rms)  <- nomRel nom (es <+> les) Nothing 
>         let ms = case  null nom of
>                        True   -> tms
>                        _      -> rms
>         return (tn : rn, Nothing , trail tsp,  ms)
>       (Just (_, xs, Just (top, nom, sp, es))) ->
>         case matchUp (xs :<
>                           (top, nom, sp, (F0, F0))) (fst $ foo 0 (trail tsp)) of
>             Nothing -> Nothing
>             Just (top', nom', i, fsc) -> do
>               let mnom = take (length nom' - length nom) nom'
>               (tn,  tms)  <- nomTop top' (mesus, mes <+> les)
>               (an,  ams)  <- nomAbs mnom fsc
>               (rn,  rms)  <- nomRel nom (es <+> les) Nothing 
>               let ms = case  (null nom,  null mnom) of
>                        (True,      True)   -> tms
>                        (True,      False)  -> ams
>                        (False,     _)      -> rms
>               return ((tn : an) ++ rn, Just i , drop (bwdLength i) (trail tsp), fmap (stripScheme (bwdLength i)) ms)
>       (Just (_, xs, _)) -> do
>         let (top', nom', i, fsc) = fromJust $ matchUp xs (fst $ foo 0 $ trail tsp) 
>         (tn, tms) <- nomTop top' (mesus, mes <+> les)
>         (an, ams) <- nomAbs nom' fsc
>         return ((tn : an), Just i,drop (bwdLength i) (trail tsp), fmap (stripScheme (bwdLength i)) (if null nom' then tms else ams))

>       _ -> Nothing 

>   case os of
>     Nothing -> return (nn, Nothing, ns, Nothing)
>     Just i -> do
>       ty <- spInf lev (D d :$ B0 :<: defTy d) (ENil, trail i)
>       return (nn, Just ty, ns, ms)

> foo :: Int -> [ Elim EXP ] -> (Int, Bool)
> foo i [] = (i, True)
> foo i (A a : as) | P (l, _, _) :$ B0 <- ev a , i == l = foo (i + 1) as
> foo i _ = (i, False) 

\paragraph{Parting the noms}

\question{Does anyone know what this does?}

> partNoms :: Name -> BScopeContext -> Name -> HypState 
>                  -> Bwd (Name, Name, Bwd (Elim EXP), FScopeContext)
>                  -> Maybe ( HypState
>                           , Bwd (Name, Name, Bwd (Elim EXP), FScopeContext) 
>                           , Maybe (Name,Name, Bwd (Elim EXP), Entries) ) 
> partNoms [] bsc _ hs xs = Just (hs, xs, Nothing)
> partNoms nom@(top:rest) bsc n hs xs = case partNom n top bsc (F0,F0) of
>  Just (sp, Left es, hs') -> Just (max hs hs', xs, Just (n ++ [top], rest, sp, es))
>  Just (sp, Right fsc, hs') -> 
>    partNoms rest bsc (n ++ [top]) (max hs hs') (xs:<(n ++ [top], rest, sp, fsc))
>  Nothing -> Nothing


> partNom :: Name -> (String, Int) -> BScopeContext -> FScopeContext
>                 -> Maybe (Bwd (Elim EXP), Either Entries FScopeContext, HypState)
> partNom hd top ((esus :< (es,top',hs)), B0) fsc | hd ++ [top] == (flatNom esus []) ++ [top'] =
>   Just (paramSpine (flat esus es),Right fsc, hs)
> partNom hd top ((esus :< (es,not,hs)), B0) (js,vjss) =
>   partNom hd top (esus,es) (F0,(not,hs,js):>vjss)
> partNom hd top (esus, es :< EModule n (Dev {devEntries=es',devHypState=hs})) fsc 
>     | (hd ++ [top]) == n =
>   Just (paramSpine (flat esus es),Left es',hs)
> partNom hd top (esus, es :< EDef d (Dev {devEntries=es',devHypState=hs}) _) fsc 
>     | hd ++ [top] == defName d =
>   Just (paramSpine (flat esus es),Left es',hs)
> partNom hd top (esus, es :< e) (fs, vfss)  = partNom hd top (esus, es) (e:>fs,vfss)
> partNom _ _ _ _ = Nothing


\paragraph{Matching up}

If we have a backward list of gibberish and a spine, it is not hard to go
back until the spine from the gibberish is a prefix of the given spine,
then return the gibberish.

> matchUp :: Bwd (Name, Name, Bwd (Elim EXP), FScopeContext) 
>              -> Int 
>              -> Maybe (Name, Name, Bwd (Elim EXP), FScopeContext)
> matchUp (xs :< (x, nom, sp, fsc)) tas
>     | bwdLength sp <= tas  = Just (x, nom, sp, fsc)
> matchUp (xs :< _) tas      = matchUp xs tas
> matchUp _ _ = Nothing

\paragraph{Different name}

First, |nomTop| handles the section where the name differs from our current
position. We call it by its |lastNom| but need to look up the offset and
scheme.

> nomTop :: Name -> BScopeContext -> Maybe ((String,Offs),Maybe Scheme)
> nomTop n bsc = do
>     (i, ms) <- countB 0 n bsc
>     return ((lastNom n, Rel i), ms)

To determine the relative offset, |nomTop| uses |countB|, which looks backwards
through the context, counting the number of things in scope with the same last
name component. This also returns the scheme attached, if there is one.

> countB :: Int -> Name -> BScopeContext -> Maybe (Int, Maybe Scheme)
> countB i n (esus :< (es', u',_), B0)
>   | last n == u' && flatNom esus [] == init n  = (| (i, Nothing) |)
> countB i n (esus :< (es', u',_), B0)
>   | lastNom n == fst u'                        = countB (i+1)  n (esus, es')
> countB i n (esus :< (es', u',_), B0)             = countB i      n (esus, es')
>
> countB i n (esus, es :< EModule n' (Dev {devEntries=es'}))
>   | n == n'                                    = (| (i, Nothing) |)
> countB i n (esus, es :< EModule n' _)           
>   | lastNom n == lastNom n'                    = countB (i+1) n (esus, es)
> countB i n (esus, es :< EDef d (Dev {devEntries=es'}) ms)
>   | n == defName d                             = (| (i, ms) |)
> countB i n (esus, es :< EDef d _ _)           
>   | lastNom n == lastNom (defName d)           = countB (i+1) n (esus, es)
> countB i n (esus, es :< e@(EParam k s t l))
>   | lastNom n == s                             = countB (i+1) n (esus, es)
>
> countB i n (esus, es :< _)                     = countB i n (esus, es)
>
> countB _ n _                                   = Nothing



\paragraph{Same name, different spine}

Next, |nomAbs| handles the section where the name is the same as the current
location but the spine is different.

> nomAbs :: Name -> FScopeContext -> Maybe (RelName, Maybe Scheme)
> nomAbs [u] (es,uess) = do
>   (v,ms) <- findF 0 u es
>   (| ([v],ms) |)
> nomAbs ((x,_):nom) (es,(_,_,es'):>uess) = do 
>   (nom',ms) <- nomAbs nom (es',uess)
>   case countF x es of
>     0 -> (| ((x,Rel 0) : nom', ms) |)
>     j -> (| ((x,Abs j) : nom', ms) |)
> nomAbs [] _ = Just ([], Nothing)
> nomAbs _ _ = Nothing

> countF :: String -> Fwd (Entry Bwd) -> Int
> countF x F0 = 0
> countF x (EModule n _ :> es) | (fst . last $ n) == x = 1 + countF x es
> countF x (EDef d _ _ :> es) | (fst . last $ defName d) == x = 1 + countF x es
> countF x (EParam _ s _ _ :> es) | s == x = 1 + countF x es
> countF x (_ :> es) = countF x es


> findF :: Int -> (String,Int) -> Fwd (Entry Bwd) 
>              -> Maybe ((String,Offs), Maybe Scheme)
> findF i u (EModule n _ :> es) | (last $ n) == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), Nothing)
> findF i u@(x,_) (EModule n _ :> es) | (fst . last $ n) == x = findF (i+1) u es
> findF i u (EDef d _ sch  :> es) | last (defName d) == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), sch)
> findF i u@(x,_) (EParam _ y _ _ :> es) | y == x = findF (i+1) u es
> findF i u (_ :> es) = findF i u es
> findF _ _ _ = Nothing

\paragraph{Same name and spine}

Finally, |nomRel| handles the section where the name and spine both match the
current location.

> nomRel :: Name -> Entries 
>                -> Maybe Scheme -> Maybe (RelName, Maybe Scheme) 
> nomRel [] _ ms = (| ([], ms) |)
> nomRel (x : nom) es _ = do
>   (i,es',ms) <- nomRel' 0 x es
>   (nom',ms') <- nomRel nom es' ms
>   return ((fst x,Rel i):nom',ms')

> nomRel' :: Int -> (String,Int) -> Entries 
>                -> Maybe (Int,Entries, Maybe Scheme)
> nomRel' o (x,i) (es:< EModule n (Dev {devEntries=es'})) | (fst . last $ n) == x  = 
>   if i == (snd . last $ n) then (| (o,es',Nothing) |) 
>                            else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:< e@(EDef d (Dev {devEntries=es'}) sch)) | (fst . last $ defName d) == x =
>   if i == (snd . last $ defName d) then (| (o,es',sch) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:< EParam _ y _ _) | y == x = nomRel' (o+1) (x,i) es
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

< christenName :: BScopeContext -> Name -> RKind -> RelName
< christenName bsc target rk = s
<   where (s, _, _) = unresolve target rk (paramSpine . (uncurry flat) $ bsc) bsc B0
<
< christenREF :: BScopeContext -> REF -> RelName
< christenREF bsc (target := rk :<: _) = christenName bsc target rk


The |showEntries| function folds over a bunch of entries, christening
them with the given entries in scope and current name, and
intercalating to produce a comma-separated list.

< showEntries :: (Traversable f, Traversable g) => BScopeContext -> f (Entry g) -> String
< showEntries bsc = intercalate ", " . foldMap f
<   where
<     f e | Just r <- entryDef e  = [showRelName (christenREF bsc r)]
<         | otherwise             = []

The |showEntriesAbs| function works similarly, but uses absolute names instead of
christening them.

> showEntriesAbs :: Traversable f => f (Entry f) -> String
> showEntriesAbs = intercalate ", " . foldMap f
>   where
>     f (EDef def _ _)      = [showName (defName def)]
>     f (EParam _ x _ l)  = [x ++ " (" ++ show l ++ ")"]
>     f (EModule n _)     = [showName n]



