\section{Naming}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, PatternGuards #-}

> module DisplayLang.Naming where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable hiding (elem, find)
> import Data.List
> import Data.Maybe
> import Data.Monoid
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import ProofState.Developments
> import ProofState.ProofContext

> import DisplayLang.DisplayTm

> import Evidences.Tm
> import Evidences.Rules
> import Evidences.Mangler

%endif

\subsection{The Naming of Things}

For display and storage purposes, we have a system of local longnames for referring to entries.
Any component of a local name may have a \textasciicircum|n| or |_n| suffix, where |n| is
an integer, representing a relative or absolute offset. A relative
offset \textasciicircum|n| refers to the $n^\mathrm{th}$ occurrence of the name
encountered when searching upwards, so |x|\textasciicircum|0| refers to the same reference
as |x|, but |x|\textasciicircum|1| skips past it and refers to the next thing named |x|.
An absolute offset |_n|, by contrast, refers to the exact numerical
component of the name. 

> data Offs = Rel Int | Abs Int deriving Show
> type RelName = [(String,Offs)]

> type InTmRN = InTm RelName
> type ExTmRN = ExTm RelName
> type InDTmRN = InDTm RelName
> type ExDTmRN = ExDTm RelName


The |showRelName| function converts a relative name to a string by
inserting the appropriate punctuation.

> showRelName :: RelName -> String
> showRelName = intercalate "." . map showOffName

> showOffName (x, Rel 0) = x
> showOffName (x, Rel i) = x ++ "^" ++ show i
> showOffName (x, Abs i) = x ++ "_" ++ show i

The |showName| function converts a name to a string absolutely (without christening).

> showName :: Name -> String
> showName = showRelName . map (\(x, i) -> (x, Abs i))


The |showEntries| function folds over a bunch of entries, christening them with the
given auncles and current name, and intercalating to produce a comma-separated list.

> showEntries :: (Traversable f, Traversable g) => BScopeContext -> f (Entry g) -> String
> showEntries bsc = intercalate ", " . foldMap
>     (\(E ref _ _ _) -> [showRelName (christenREF bsc ref)])

The |showEntriesAbs| function works similarly, but uses absolute names instead of
christening them.

> showEntriesAbs :: Traversable f => f (Entry f) -> String
> showEntriesAbs = intercalate ", " . foldMap f
>   where
>     f e = [showName (entryName e)]


\subsection{Resolving Local Longnames}

We need to resolve local longnames as
references. We resolve \(f.x.y.z\) by searching outwards for $f$, then
inwards for a child $x$, $x$'s child $y$, $y$'s child $z$. References
are fully $\lambda$-lifted, but as $f$'s parameters are held in common
with the point of reference, we automatically supply them.

\subsection{A New Hope}

This needs documenting I (Peter) am on it.

> resolve :: RelName -> Maybe BScopeContext -> FScopeContext -> 
>             Either (StackError t) (REF, Spine {TT} REF, Maybe (Scheme INTM))
> resolve [(y, Rel 0)] _ _
>   | Just ref <- lookup y primitives = Right (ref, [], Nothing)
>   | Just ref <- lookup y axioms     = Right (ref, [], Nothing)
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
> lookUp (x,i) (esus, es :< e@(E r (y,j) (Girl _ (es',_,_) ms) _)) (fs,vfss) | x == y =
>   if i == 0 then Right (Right es', boySpine (flat esus es), Just r, ms)
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
> lookDown (x, i) (E r (y, _) (Girl _ (es', _, _) ms) _ :> es , uess) sp | x == y =
>   if i == 0 then Right (Right es', sp, Just r, ms) 
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
> lookUpLocal (x, i) ys (xs :< E r (y,j) e@(Girl _ (es,_,_) ms) _) as | x == y = 
>     if i == 0 then lookLocal ys es as (Just r) ms
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
> lookDownLocal (x, i) ys (E r (y,j) e@(Girl _ (es,_,_) ms) _ :> xs) as | x == y = 
>     if i == 0 then lookLocal ys es as (Just r) ms
>               else lookDownLocal (x,i-1) ys xs as
> lookDownLocal (x, i) ys (E r (y,j) (Boy _) _ :> xs) as | x == y = 
>     if i == 0 then Left  [err "Boys in other Devs are not in scope"]
>               else lookDownLocal (x,i-1) ys xs as
> lookDownLocal (x, i) ys (e :> xs) as = lookDownLocal (x, i) ys xs as 
> lookDownLocal (x, i) ys F0 as = Left  [err $ "Had to give up looking for " ++ x]


\subsection{Christening (Generating Local Longnames)}

Just as resolution automatically supplies parameters to references
which are actually lifted, so its inverse, \emph{christening}, must
hide parameters to lifted references which can be seen locally. For
example, here

\begin{alltt}
f [
  x : S
  g => t : T
  ] => g : T
\end{alltt}

$g$ is actually represented as $f.g f.x$, but should be displayed as, er, $g$.

The |christenName| and |christenREF| functions do a similar job for names, and
the name part of references, respectively.

> christenName :: BScopeContext -> Name -> RKind -> RelName
> christenName bsc target rk = s
>   where (s, _, _) = unresolve target rk (boySpine . (uncurry flat) $ bsc) bsc B0
>
> christenREF :: BScopeContext -> REF -> RelName
> christenREF bsc (target := rk :<: _) = christenName bsc target rk


> failNom :: Name -> RelName
> failNom nom = ("!!!",Rel 0):(map (\(a,b) -> (a,Abs b)) nom)

> type BwdName = Bwd (String,Int)

> unresolve :: Name -> RKind -> Spine {TT} REF -> BScopeContext
>                   -> Entries -> (RelName, Int, Maybe (Scheme INTM))
> unresolve tar DECL _ (esus,es) les = 
>   case find ((tar ==) . refName . snd) (axioms ++ primitives) of
>     Just (s, _)  -> ([(s, Rel 0)], 0, Nothing)
>     Nothing      -> maybe (failNom tar,0,Nothing) id 
>                       (nomTop tar (esus, es<+>les) >>= 
>                         \(x,_) -> (| ([x],0,Nothing) |))
> unresolve tar rk tas msc@(mesus,mes) les = 
>   case find ((tar ==) . refName . snd) (axioms ++ primitives) of
>     Just (s, _)  -> ([(s, Rel 0)], 0, Nothing)
>     Nothing      -> case (partNoms tar msc [] B0, rk) of
>       (Just (xs,Just (top,nom,sp,es)),_) | sp `isPrefixOf` tas ->
>         maybe (failNom tar,0,Nothing) id 
>           (do (tn, tms) <- nomTop top (mesus,mes<+>les) 
>               (rn, rms) <- nomRel nom (es <+> les) [] Nothing 
>               (| (tn : rn, length sp, if null nom then tms else rms) |))
>       (Just (xs,Just (top,nom,sp,es)),_) ->
>         maybe (failNom tar,0,Nothing) id 
>           (do let (top',nom',i,fsc) = matchUp xs tas 
>               (tn,tms) <- nomTop top' (mesus,mes<+>les)
>               let mnom = take (length nom' - length nom) nom'
>               (an,ams) <- nomAbs mnom fsc
>               let tams = if null mnom then tms else ams  
>               (rn, rms) <- nomRel nom (es <+> les) [] Nothing 
>               (| ((tn : an) ++ rn, i, if null nom then tams else rms) |)) 
>       (Just (xs, Nothing),FAKE) ->
>         maybe (failNom tar,0,Nothing) id 
>           (do let (top',nom',i,fsc) = matchUp xs tas 
>               (tn,tms) <- nomTop top' (mesus,mes<+>les)
>               (an,ams) <- nomAbs nom' fsc
>               (| ((tn : an), i, if null nom' then tms else ams) |) )
>       _ -> (failNom tar, 0, Nothing)

> partNoms :: Name -> BScopeContext -> Name 
>                  -> Bwd (Name, Name, Spine {TT} REF, FScopeContext)
>                  -> Maybe ( Bwd (Name, Name, Spine {TT} REF, FScopeContext) 
>                     , Maybe (Name,Name, Spine {TT} REF, Entries) ) 
> partNoms [] bsc _ xs = Just (xs, Nothing)
> partNoms nom@(top:rest) bsc n xs = case partNom top bsc (F0,F0) of
>  Just (sp, Left es) -> Just (xs, Just (n ++ [top], rest, sp, es))
>  Just (sp, Right fsc) -> 
>    partNoms rest bsc (n ++ [top]) (xs:<(n ++ [top], rest, sp, fsc))
>  Nothing -> Nothing

> matchUp :: Bwd (Name, Name, Spine {TT} REF, FScopeContext) 
>              -> Spine {TT} REF ->  (Name, Name, Int, FScopeContext)
> matchUp (xs :< (x, nom, sp, fsc)) tas | sp `isPrefixOf` tas =
>   (x, nom, length sp, fsc)
> matchUp (xs :< _) tas = matchUp xs tas

> partNom :: (String, Int) -> BScopeContext -> FScopeContext
>                 -> Maybe (Spine {TT} REF, Either Entries FScopeContext)
> partNom top ((esus :< (es,top')), B0) fsc | top == top' =
>   Just (boySpine (flat esus es),Right fsc)
> partNom top ((esus :< (es,not)), B0) (js,vjss) =
>   partNom top (esus,es) (F0,(not,js):>vjss)
> partNom top (esus, es :< M n (es',_,_)) fsc | top == last n =
>   Just (boySpine (flat esus es),Left es')
> partNom top (esus, es :< E _ top' (Girl _ (es',_,_) _) _) fsc | top == top' =
>   Just (boySpine (flat esus es),Left es')
> partNom top (esus, es :< e) (fs, vfss)  = partNom top (esus, es) (e:>fs,vfss)
> partNom _ _ _ = Nothing

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
> findF i u (E _ v (Girl _ _ ms) _ :> es) | v == u = 
>   Just ((fst u, if i == 0 then Rel 0 else Abs i), ms)
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
> countB i n (esus,es:<E r u' (Girl _ (es',_,_) ms) _) | last n == u' &&
>                                                        refName r == n = 
>   (| (i, ms) |)
> countB i n (esus,es:<E r u' _ _) | last n == u' && refName r == n = 
>   (| (i, Nothing) |)
> countB i n (esus,es:<E _ u' _ _) | (fst . last $ n) == fst u' = 
>   countB (i+1) n (esus,es)
> countB i n (esus,es:<_) = countB i n (esus,es)
> countB _ n _ = Nothing 

> nomRel :: Name -> Entries -> RelName 
>                -> Maybe (Scheme INTM) -> Maybe (RelName, Maybe (Scheme INTM)) 
> nomRel [] _ rom ms = (| (rom, ms) |)
> nomRel (x : nom) es rom _ = do
>   (i,es',ms) <- nomRel' 0 x es
>   nomRel nom es' ((fst x,Rel i):rom) ms

> nomRel' :: Int -> (String,Int) -> Entries 
>                -> Maybe (Int,Entries, Maybe (Scheme INTM))
> nomRel' o (x,i) (es:<M n (es',_,_)) | (fst . last $ n) == x  = 
>   if i == (snd . last $ n) then (| (o,es',Nothing) |) 
>                            else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<E _ (y,j) (Girl _ (es',_,_) ms) _) | y == x =
>   if i == j then (| (o,es',ms) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<E _ (y,j) _ _) | y == x = 
>   if i == j then (| (o,B0,Nothing) |) else nomRel' (o+1) (x,i) es
> nomRel' o (x,i) (es:<e) = nomRel' o (x,i) es
> nomRel' _ _ _ = Nothing
