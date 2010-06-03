\section{Resolving and unresolving names}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, PatternGuards #-}

> module ProofState.NameResolution where

> import Control.Applicative
> import Control.Monad.State
> import Data.Foldable hiding (elem, find)
> import Data.List
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import ProofState.Developments
> import ProofState.ProofContext
> import ProofState.ProofState

> import DisplayLang.Name
> import DisplayLang.Scheme

> import Evidences.Tm
> import Evidences.Rules

%endif

\newcommand{\relname}[1]{\textit{#1}}

Typographical note: in this section, we write \relname{f} for a relative name 
(component) and @f_0@ for an absolute name (component).

A |BScopeContext| contains information from the |ProofContext| required for
name resolution: a list of the elders and last component of the mother's name
for each layer, along with the entries in the current development.

> type BScopeContext =  (Bwd (Entries, (String, Int)), Entries) 

We can extract such a thing from a |ProofContext| using |inBScope|:

> inBScope :: ProofContext -> BScopeContext
> inBScope (PC layers (entries,_,_) _) = 
>   (  fmap (\l -> (elders l, last . motherName . mother $ l)) layers
>   ,  entries)

An |FScopeContext| is the forwards variant.

> type FScopeContext =  ( Fwd (Entry Bwd)
>                       , Fwd ((String, Int), Fwd (Entry Bwd))) 
>
> inBFScope :: BScopeContext -> FScopeContext
> inBFScope (uess :< (es,u),es') = 
>   let (fs, vfss) = inBFScope (uess,es) in 
>   (fs, (u,es' <>> F0) :> vfss)
> inBFScope (B0,es) = (es <>> F0,F0) 


\subsection{Resolving relative names to references}

We need to resolve local longnames as references. We resolve \relname{f.x.y.z}
by searching outwards for \relname{f}, then inwards for a child \relname{x},
\relname{x}'s child \relname{y}, \relname{y}'s child \relname{z}. References are
fully $\lambda$-lifted, but as \relname{f}'s parameters are held in common with
the point of reference, we automatically supply them.

The |resolveHere| command resolves a relative name to a reference,
a spine of shared parameters to which it should be applied, and
possibly a scheme. If the name ends with "./", the scheme will be
discarded, so all parameters can be provided explicitly.
\question{What should the syntax be for this, and where should it be handled?}

> resolveHere :: RelName -> ProofState (REF, Spine {TT} REF, Maybe (Scheme INTM))
> resolveHere x = do
>     pc <- get
>     let  x'    = if fst (last x) == "/" then init x else x
>          uess  = inBScope pc
>     ans@(r, s, ms) <- resolve x' (Just $ uess) (inBFScope uess)  
>        `catchEither` (err $ "resolveHere: cannot resolve name: "
>                             ++ showRelName x')
>     if fst (last x) == "/" then return (r, s, Nothing) else return ans

The |resolveDiscard| command resolves a relative name to a reference,
discarding any shared parameters it should be applied to.

> resolveDiscard :: RelName -> ProofState REF
> resolveDiscard x = resolveHere x >>= (\ (r, _, _) -> return r)


There are four stages relating to whether we are looking up or down
(\relname{\^} or \relname{\_})
and whether or nor we are navigating the part of the proof state which is on the
way back to (or from) the root of the tree to the cursor position.
\question{Which is which?}

> resolve :: RelName -> Maybe BScopeContext -> FScopeContext -> 
>             Either (StackError t) (REF, Spine {TT} REF, Maybe (Scheme INTM))
> resolve [(y, Rel 0)] _ _
>   | Just ref <- lookup y primitives = Right (ref, [], Nothing)
> resolve us bsc fsc = lookFor us bsc fsc


> lookFor :: RelName -> Maybe BScopeContext -> FScopeContext -> 
>            Either (StackError t) (REF, Spine {TT} REF, Maybe (Scheme INTM))
> lookFor ((x,Rel i):us) (Just bsc) fsc = lookUp (x,i) bsc fsc >>= (lookFor' us)
> lookFor ((x,Rel 0):us) _ fsc = lookDown (x,0) fsc [] >>= (lookFor' us)
> lookFor ((x,Rel i):us) Nothing fsc = Left [err "Yeah, good luck with that"]
> lookFor ((x,Abs i):us) _ fsc = lookDown (x,i) fsc [] >>= (lookFor' us)

> lookFor' :: RelName -> ( Either FScopeContext Entries
>                        , Spine {TT} REF
>                        , Maybe REF 
>                        , Maybe (Scheme INTM)) ->
>             Either (StackError t) (REF, Spine {TT} REF, Maybe (Scheme INTM))
> lookFor' us (Left fsc,sp,Nothing,_) | null us = 
>   Left [err "Direct ancestors are not in scope!"]
> lookFor' us (_,sp,Just r,ms) | null us  = Right (r,sp,ms) 
> lookFor' us (Left fsc,sp,_,_) = do 
>   (x,_,z) <- lookFor us Nothing fsc
>   return (x,sp,z)
> lookFor' us (Right es,sp,mr,ms) = lookLocal us es sp mr ms

> flat :: Bwd (Entries, (String,Int)) -> Entries -> Entries
> flat B0 es = es
> flat (esus :< (es',_)) es = flat esus (es' <+> es)

> flatNom :: Bwd (Entries, (String,Int)) -> Name -> Name
> flatNom B0 nom = nom
> flatNom (esus :< (_,u)) nom = flatNom esus (u : nom)

> lookUp :: (String, Int) -> BScopeContext -> FScopeContext -> 
>                            Either (StackError t) 
>                                   ( Either FScopeContext Entries
>                                   , Spine {TT} REF
>                                   , Maybe REF 
>                                   , Maybe (Scheme INTM))
> lookUp (x,i) (B0,B0) fs = Left [err $ "Not in scope " ++ x]
> lookUp (x,i) ((esus :< (es,(y,j))),B0) (fs,vfss) | x == y = 
>   if i == 0 then Right (Left (fs,vfss), boySpine (flat esus es), Nothing, Nothing)
>             else lookUp (x,i-1) (esus,es) (F0,((y,j),fs) :> vfss)
> lookUp (x,i) ((esus :< (es,(y,j))),B0) (fs,vfss) = 
>   lookUp (x,i) (esus,es) (F0,((y,j),fs) :> vfss)
> lookUp (x,i) (esus, es :< e@(M n (es', _, _))) (fs,vfss) | (fst $ last n) == x =
>   if i == 0 then Right (Right es', boySpine (flat esus es), Nothing, Nothing)
>             else lookUp (x,i-1) (esus,es) (e:>fs,vfss)
> lookUp (x,i) (esus, es :< e@(E r (y,j) (Girl kind (es',_,_)) _)) (fs,vfss) | x == y =
>   if i == 0 then Right (Right es', boySpine (flat esus es), Just r, kindScheme kind)
>             else lookUp (x,i-1) (esus,es) (e:>fs,vfss)
> lookUp (x,i) (esus, es :< e@(E r (y,j) (Boy _) _)) (fs,vfss) | x == y =
>   if i == 0 then Right (Right B0, [], Just r, Nothing)
>             else lookUp (x,i-1) (esus,es) (e:>fs,vfss)
> lookUp u (esus, es :< e) (fs,vfss) = lookUp u (esus,es) (e:>fs,vfss)

> lookDown :: (String,Int) -> FScopeContext -> Spine {TT} REF -> 
>                             Either (StackError t) 
>                                    ( Either FScopeContext Entries
>                                    , Spine {TT} REF
>                                    , Maybe REF
>                                    , Maybe (Scheme INTM) )
> lookDown (x,i) (F0,F0) fs = Left [err $ "Not is scope " ++ x]
> lookDown (x, i) (M n (es', _, _) :> es , uess) sp | x == (fst $ last n) =
>   if i == 0 then Right (Right es', sp, Nothing, Nothing) 
>             else lookDown (x, i-1) (es, uess) sp 
> lookDown (x, i) (E r (y, _) (Girl kind (es', _, _)) _ :> es , uess) sp | x == y =
>   if i == 0 then Right (Right es', sp, Just r, kindScheme kind) 
>             else lookDown (x, i-1) (es, uess) sp
> lookDown (x, i) (E r (y, _) (Boy _) _ :> es , uess) sp | x == y =
>   if i == 0 then Right (Right B0, [], Just r, Nothing) 
>             else lookDown (x, i-1) (es,uess) (A (N (P r)) : sp)
> lookDown u (E r _ (Boy _) _ :> es, uess) sp = 
>   lookDown u (es, uess) (A (N (P r)) : sp)
> lookDown u (_ :> es, uess) sp = lookDown u (es, uess) sp
> lookDown (x, i) (F0 , (((y, j),es) :> uess)) sp | x == y =
>   if i == 0 then Right (Left (es,uess), sp, Nothing, Nothing)
>             else lookDown (x, i-1) (es, uess) sp
> lookDown u (F0, ((_,es) :> uess)) sp = lookDown u (es, uess) sp 


> lookLocal :: RelName -> Entries -> Spine {TT} REF -> 
>              Maybe REF -> Maybe (Scheme INTM) -> 
>                           Either (StackError t) 
>                                  (REF, Spine {TT} REF, Maybe (Scheme INTM))
> lookLocal ((x, Rel i) : ys) es sp _ _ = lookUpLocal (x,i) ys es sp
> lookLocal ((x, Abs i) : ys) es sp _ _ = lookDownLocal (x,i) ys (es <>> F0) sp 
> lookLocal [] _ sp (Just r) ms = Right (r, sp, ms)
> lookLocal [] _ _ Nothing _ = Left [err "Modules have not term representaion"]

> lookUpLocal :: (String,Int) -> RelName -> Entries -> Spine {TT} REF -> 
>                           Either (StackError t) 
>                                  (REF, Spine {TT} REF, Maybe (Scheme INTM))
> lookUpLocal (x, i) ys (xs :< M n (es, _, _)) as | x == (fst $ last n) =
>     if i == 0 then lookLocal ys es as Nothing Nothing
>               else lookUpLocal (x,i-1) ys xs as
> lookUpLocal (x, i) ys (xs :< E r (y,j) e@(Girl kind (es,_,_)) _) as | x == y = 
>     if i == 0 then lookLocal ys es as (Just r) (kindScheme kind)
>               else lookUpLocal (x,i-1) ys xs as
> lookUpLocal (x, i) ys (xs :< E r (y,j) (Boy _) _) as | x == y = 
>     if i == 0 then Left  [err "Boys in other Devs are not in scope"]
>               else lookUpLocal (x,i-1) ys xs as 
> lookUpLocal (x, i) ys (xs :< e) as = lookUpLocal (x, i) ys xs as 
> lookUpLocal (x, i) ys B0 as = Left  [err $ "Had to give up looking for " ++ x]

> lookDownLocal :: (String,Int) -> RelName -> Fwd (Entry Bwd) -> 
>                  Spine {TT} REF ->
>                  Either (StackError t) 
>                         (REF, Spine {TT} REF, Maybe (Scheme INTM))
> lookDownLocal (x, i) ys (M n (es, _, _) :> xs) as | x == (fst $ last n) =
>     if i == 0 then lookLocal ys es as Nothing Nothing
>               else lookDownLocal (x,i-1) ys xs as
> lookDownLocal (x, i) ys (E r (y,j) e@(Girl kind (es,_,_)) _ :> xs) as | x == y = 
>     if i == 0 then lookLocal ys es as (Just r) (kindScheme kind)
>               else lookDownLocal (x,i-1) ys xs as
> lookDownLocal (x, i) ys (E r (y,j) (Boy _) _ :> xs) as | x == y = 
>     if i == 0 then Left  [err "Boys in other Devs are not in scope"]
>               else lookDownLocal (x,i-1) ys xs as
> lookDownLocal (x, i) ys (e :> xs) as = lookDownLocal (x, i) ys xs as 
> lookDownLocal (x, i) ys F0 as = Left  [err $ "Had to give up looking for " ++ x]


\subsection{Unresolving absolute names to relative names}
\label{subsec:christening}

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

How should we print the computer name @X_0.f_0.g_0@ ? A first approximation 
would be \relname{g} since this is the bit that differs from the name of the
development we are in (@X_0.f_0@). And, indeed we will always have to print this
bit of the name. But there's more to it, here we are assuming that we are
applying @g@  to the same spine of boys as the boys we are currently working
under, which isn't always true. We need to be able to refer to, for instance,
\relname{f.g}, which would have type |(b : B) -> T|. So we must really resolve
names with their spines compared to the current name and boy spine. So:
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

The |christenName| and |christenREF| functions call |unresolve| for names, and
the name part of references, respectively.

> christenName :: BScopeContext -> Name -> RKind -> RelName
> christenName bsc target rk = s
>   where (s, _, _) = unresolve target rk (boySpine . (uncurry flat) $ bsc) bsc B0
>
> christenREF :: BScopeContext -> REF -> RelName
> christenREF bsc (target := rk :<: _) = christenName bsc target rk


The |failNom| function is used to give up and convert an absolute name that
cannot be unresolved into a relative name. This can happen when distilling
erroneous terms, which may not be well-scoped.

> failNom :: Name -> RelName
> failNom nom = ("!!!",Rel 0):(map (\(a,b) -> (a,Abs b)) nom)


A |BwdName| is, as one might expect, a |Name| stored backwards.

> type BwdName = Bwd (String,Int)

To |unresolve| an absolute |Name|, we need its reference kind, the spine of
arguments to which it is applied, the context in which we are viewing it and
a list of entries in local scope. We obtain a relative name, the number of
shared parameters to drop, and the scheme of the name (if there is one).

> unresolve :: Name -> RKind -> Spine {TT} REF -> BScopeContext
>                   -> Entries -> (RelName, Int, Maybe (Scheme INTM))
> unresolve tar DECL _ (esus,es) les = 
>   case find ((tar ==) . refName . snd) primitives of
>     Just (s, _)  -> ([(s, Rel 0)], 0, Nothing)
>     Nothing      -> maybe (failNom tar,0,Nothing) id 
>                       (nomTop tar (esus, es<+>les) >>= 
>                         \(x,_) -> (| ([x],0,Nothing) |))
> unresolve tar rk tas msc@(mesus,mes) les = 
>   case find ((tar ==) . refName . snd) primitives of
>     Just (s, _)  -> ([(s, Rel 0)], 0, Nothing)
>     Nothing      -> case (partNoms tar msc [] B0, rk) of
>       (Just (xs,Just ys@(top,nom,sp,es)),_) ->
>         maybe (failNom tar,0,Nothing) id 
>           (do let (top',nom',i,fsc) = matchUp xs ys tas 
>               (tn,tms) <- nomTop top' (mesus,mes<+>les)
>               let mnom = take (length nom' - length nom) nom'
>               (an,ams) <- nomAbs mnom fsc
>               let tams = if null mnom then tms else ams  
>               (rn, rms) <- nomRel nom (es <+> les) Nothing 
>               (| ((tn : an) ++ rn, i, if null nom then tams else rms) |)) 
>       (Just (xs, Nothing),FAKE) ->
>         maybe (failNom tar,0,Nothing) id 
>           (do let (top',nom',i,fsc) = matchUp' xs tas 
>               (tn,tms) <- nomTop top' (mesus,mes<+>les)
>               (an,ams) <- nomAbs nom' fsc
>               (| ((tn : an), i, if null nom' then tms else ams) |) )
>       _ -> (failNom tar, 0, Nothing)

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

> matchUp :: Bwd (Name, Name, Spine {TT} REF, FScopeContext) ->
>              (Name,Name, Spine {TT} REF, Entries) ->
>              Spine {TT} REF ->  (Name, Name, Int, FScopeContext)
> matchUp blah (x,y,sp,es) tas | sp `isPrefixOf` tas =
>   (x,y,length sp,(F0,F0))
> matchUp blah _ tas = matchUp' blah tas

> matchUp' :: Bwd (Name, Name, Spine {TT} REF, FScopeContext) 
>              -> Spine {TT} REF ->  (Name, Name, Int, FScopeContext)
> matchUp' (xs :< (x, nom, sp, fsc)) tas | sp `isPrefixOf` tas =
>   (x, nom, length sp, fsc)
> matchUp' (xs :< _) tas = matchUp' xs tas

> partNom :: Name -> (String, Int) -> BScopeContext -> FScopeContext
>                 -> Maybe (Spine {TT} REF, Either Entries FScopeContext)
> partNom hd top ((esus :< (es,top')), B0) fsc | hd ++ [top] == (flatNom esus []) ++ [top'] =
>   Just (boySpine (flat esus es),Right fsc)
> partNom hd top ((esus :< (es,not)), B0) (js,vjss) =
>   partNom hd top (esus,es) (F0,(not,js):>vjss)
> partNom hd top (esus, es :< M n (es',_,_)) fsc | (hd ++ [top]) == n =
>   Just (boySpine (flat esus es),Left es')
> partNom hd top (esus, es :< E _ top' (Girl _ (es',_,_)) _) fsc | hd ++ [top] == (flatNom esus []) ++ [top'] =
>   Just (boySpine (flat esus es),Left es')
> partNom hd top (esus, es :< e) (fs, vfss)  = partNom hd top (esus, es) (e:>fs,vfss)
> partNom _ _ _ _ = Nothing

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
> countF x (M n _ :> es) | (fst . last $ n) == x = 1 + countF x es
> countF x (E _ (y,_) _ _ :> es) | y == x = 1 + countF x es
> countF x (_ :> es) = countF x es

> findF :: Int -> (String,Int) -> Fwd (Entry Bwd) 
>              -> Maybe ((String,Offs), Maybe (Scheme INTM))
> findF i u (M n _ :> es) | (last $ n) == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), Nothing)
> findF i u@(x,_) (M n _ :> es) | (fst . last $ n) == x = findF (i+1) u es
> findF i u (E _ v (Girl kind _) _ :> es) | v == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), kindScheme kind)
> findF i u (E _ v _ _ :> es) | v == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), Nothing)
> findF i u@(x,_) (E _ (y,_) _ _ :> es) | y == x = findF (i+1) u es
> findF i u (_ :> es) = findF i u es
> findF _ _ _ = Nothing

> nomTop :: Name -> BScopeContext -> Maybe ((String,Offs),Maybe (Scheme INTM))
> nomTop n bsc = do
>   (i,ms) <- countB 0 n bsc
>   (| ((fst . last $ n, Rel i), ms) |)

> countB :: Int -> Name -> BScopeContext -> Maybe (Int, Maybe (Scheme INTM))
> countB i n (esus:<(es',u'),B0) | u' == last n && 
>                                  flatNom esus [] == init n = (| (i,Nothing) |)
> countB i n (esus:<(es',u'),B0) | fst u' == (fst . last $ n) = 
>   countB (i+1) n (esus,es')
> countB i n (esus:<(es',u'),B0) = countB i n (esus,es')
> countB i n (esus,es:<M n' (es',_,_)) | n == n' = (| (i, Nothing) |)
> countB i n (esus,es:<M n' _) | (fst . last $ n') == (fst . last $ n) =
>   countB (i+1) n (esus,es)
> countB i n (esus,es:<E r u' (Girl kind (es',_,_)) _) | last n == u' &&
>                                                        refName r == n = 
>   (| (i, kindScheme kind) |)
> countB i n (esus,es:<E r u' _ _) | last n == u' && refName r == n = 
>   (| (i, Nothing) |)
> countB i n (esus,es:<E _ u' _ _) | (fst . last $ n) == fst u' = 
>   countB (i+1) n (esus,es)
> countB i n (esus,es:<_) = countB i n (esus,es)
> countB _ n _ = Nothing 

> nomRel :: Name -> Entries 
>                -> Maybe (Scheme INTM) -> Maybe (RelName, Maybe (Scheme INTM)) 
> nomRel [] _ ms = (| ([], ms) |)
> nomRel (x : nom) es _ = do
>   (i,es',ms) <- nomRel' 0 x es
>   (nom',ms') <- nomRel nom es' ms
>   return ((fst x,Rel i):nom',ms')

> nomRel' :: Int -> (String,Int) -> Entries 
>                -> Maybe (Int,Entries, Maybe (Scheme INTM))
> nomRel' o (x,i) (es:<M n (es',_,_)) | (fst . last $ n) == x  = 
>   if i == (snd . last $ n) then (| (o,es',Nothing) |) 
>                            else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<E _ (y,j) (Girl kind (es',_,_)) _) | y == x =
>   if i == j then (| (o,es',kindScheme kind) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<E _ (y,j) _ _) | y == x = 
>   if i == j then (| (o,B0,Nothing) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<e) = nomRel' o (x,i) es
> nomRel' _ _ _ = Nothing




The |showEntries| function folds over a bunch of entries, christening them with
the given auncles and current name, and intercalating to produce a
comma-separated list.

> showEntries :: (Traversable f, Traversable g) => BScopeContext -> f (Entry g) -> String
> showEntries bsc = intercalate ", " . foldMap
>     (\(E ref _ _ _) -> [showRelName (christenREF bsc ref)])

The |showEntriesAbs| function works similarly, but uses absolute names instead of
christening them.

> showEntriesAbs :: Traversable f => f (Entry f) -> String
> showEntriesAbs = intercalate ", " . foldMap f
>   where
>     f e = [showName (entryName e)]