\label{sec:Elaboration.Ambulando}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, PatternGuards #-}

> module Elaboration.Ambulando where

> import Prelude hiding (exp, all, any, elem)

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (foldr)

> import Evidences.Tm
> import Evidences.News
> import Evidences.EtaQuote
> import Evidences.ErrorHandling

> import ProofState.Structure
> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation
> import ProofState.Interface

> import Elaboration.NewElabMonad
> import Elaboration.NewRunElab

> import Data.List hiding (all, any, elem)

> import Kit.NatFinVec
> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Debug.Trace

%endif


> ambulando :: Maybe Name -> NewsBulletin -> ProofState ()
> ambulando nam news = do
>   NF cs <- getBelowCursor
>   putBelowCursor (NF F0)
>   ambulando' nam cs news


> ambulando' :: Maybe Name -> Fwd (Either NewsBulletin (Entry NewsyFwd)) 
>                          -> NewsBulletin -> ProofState ()
> ambulando' nam F0 news = do

>   nom <- getCurrentName

We are at the end of the current layer, we should update the tip on the news:

>   tip <- getDevTip
>   tT <- tellTip nom news tip 

This can go two ways, if the tip has an elaboration problem which is
requesting a hole to be filled we should go do that immediately. Otherwise,
we get a new copy of the tip and we should update the def based on that:

>   case tT of
>     Right (tip', nnews) -> do
>       putDevTip tip'
>       news' <- case nnews of
>         NoNews -> (| news |)
>         _ -> do
>           (d,_) <- updateDefFromTip
>           (| (addGirlNews (d,nnews) news) |)

Check if we have reached our destination:

>       if nam == Just nom 

If so we stash the latest news in the containing layer:

>         then  putNewsBelow news'

Or we exit this layer and continue working down and out:

>         else do
>           -- go out
>           currentEntry <- getCurrentEntry
>           dev <- getAboveCursor
>           e <- case currentEntry of
>             CDefinition def sch -> return $ EDef def dev sch
>             CModule n           -> return $ EModule n dev
>           mLayer <- optional removeLayer
>           case mLayer of
>            Just l ->  do
>              putAboveCursor $ Dev  {  devEntries       =  aboveEntries l :< e
>                                    ,  devTip           =  layTip l
>                                    ,  devNSupply       =  layNSupply l
>                                    ,  devLevelCount    =  layLevelCount l
>                                    ,  devHypState      =  layHypState l
>                                    }
>              ambulando' nam (unNF $ belowEntries l) news'
>            Nothing -> (| () |)

In the other case we need to do some instantiation, so we drop what we are
currently doing and zoom out to deal with that.

>     Left (n, e) -> do
>       putNewsBelow news
>       odnalubma n e 
>       ambulando nam NONEWS

If we find some news, we combine it with the stuff we already knew:

> ambulando' nam (Left news' :> belowE) news = 
>   ambulando' nam belowE (mergeNews news' news)


If we encounter a parameter, we should find out if it's type has got more
informative, and then continue:

> ambulando' nam (Right (EParam w x y z) :> belowE) news = do
>   above <- getEntriesAbove
>   let (e',news') = tellParamEntry news (EParam w x y z)
>   putEntriesAbove (above :< e')
>   ambulando' nam belowE news'

Anything else we encounter will be a definition or a module, in either case
we should go in and update everyone on the news.

> ambulando' nam (Right e :> belowE) news = do
>   let Just dv = entryDev e -- this is ok, since we already dealt with the Params
>   oldFocus  <- getAboveCursor
>   putLayer $ Layer {  aboveEntries     = devEntries oldFocus
>                    ,  currentEntry     = mkCurrentEntry e
>                    ,  belowEntries     = NF belowE
>                    ,  layTip           = devTip oldFocus
>                    ,  layNSupply       = devNSupply oldFocus
>                    ,  layLevelCount    = devLevelCount oldFocus
>                    ,  layHypState      = devHypState oldFocus
>                    }
>   putAboveCursor $ dv {devEntries = B0}
>   ambulando' nam (unNF $ devEntries dv) news

Ok, so we are backing up looking for the hole someone wanted solving

> odnalubma :: Name -> (TY :>: EXP) -> ProofState ()
> odnalubma n e = do
>   lev <- getDevLev 
>   ez <- getEntriesAbove
>   putEntriesAbove B0
>   odnalubma' n ([],[]) lev e ez 0

> odnalubma' :: Name -> ([(DEF,Tip)],[Int]) -> Int -> (TY :>: EXP) -> 
>              Bwd (Entry Bwd) -> Int -> ProofState ()

Reached the top of the current layer without finding the target, exit to the
containing layer, continue.

> odnalubma' n (deps, ldeps) lev tm B0 nest = do
>     currentEntry <- getCurrentEntry
>     dev <- getAboveCursor
>     below <- getBelowCursor
>     e <- case currentEntry of
>       CDefinition d sch -> return $ EDef d (dev {devEntries = below}) sch
>       CModule n           -> return $ EModule n (dev {devEntries = below})
>     mLayer <- optional removeLayer
>     case mLayer of
>      Just l ->  do
>        putAboveCursor $ Dev  {  devEntries       =  B0
>                              ,  devTip           =  layTip l
>                              ,  devNSupply       =  layNSupply l
>                              ,  devLevelCount    =  layLevelCount l
>                              ,  devHypState      =  layHypState l
>                              }
>        putBelowCursor $ NF (Right e :> unNF (belowEntries l))
>        odnalubma' n (deps, pred ldeps) lev tm (aboveEntries l) (max 0 (nest-1))
>  where pred :: [ Int ] -> [ Int ]
>        pred = nub . map (max 0 . (subtract 1))

> odnalubma' n (deps, ldeps) lev tm (ez :< EParam a b c l) nest 
>       | all (< nest) ldeps , not (occurs lev Nothing [l] tm)  = do
>     below <- getBelowCursor
>     putBelowCursor (NF (Right (EParam a b c l) :> unNF below))
>     odnalubma' n (deps, ldeps) lev tm ez nest 
>       | otherwise = error "O" -- bad param


> odnalubma' n (deps, ldeps) lev (ty :>: tm) (ez :< e) nest 
>  | (Just n == entryName e) = do
>     putEntriesAbove ez
>     news <- makeDeps deps NONEWS
>     ez' <- getEntriesAbove
>     putEntriesAbove (ez' :< e)
>     goIn
>     let (tm', _) = tellNews news tm
>         tm'' = exp (ev tm')
>     def' <- give tm''
>     goOut' 
>     bc <- getBelowCursor
>     putBelowCursor (NF (Left (mergeNews news ([(def', GoodNews)], Nothing)) :> unNF bc))
>     return ()
>   where
>     makeDeps :: [(DEF, Tip)] -> NewsBulletin -> ProofState NewsBulletin
>     makeDeps [] news = return news
>     makeDeps ((old, Unknown ty k) : deps) news = do
>         let (ty', _) = tellNews news ty
>         makeKinded InheritHyps Nothing k (fst (last (defName old)) :<: ty')
>         -- seems like a crap name choice
>         EDef oldd _ _ <- getEntryAbove
>         let op = Emit (def oldd)
>         makeDeps deps (addGirlNews (old{defOp = op}, GoodNews) news)
>     makeDeps _ _ = throwError' $ err "makeDeps: bad reference kind! Perhaps "
>         ++ err "solveHole was called with a term containing unexpanded definitions?"


> odnalubma' n (deps, ldeps) lev (ty :>: tm) (ez :< e) nest = do
>     let Just dv = entryDev e
>     oldFocus  <- getAboveCursor
>     belowE <- getBelowCursor
>     putLayer $ Layer {  aboveEntries     = ez
>                      ,  currentEntry     = mkCurrentEntry e
>                      ,  belowEntries     = belowE
>                      ,  layTip           = devTip oldFocus
>                      ,  layNSupply       = devNSupply oldFocus
>                      ,  layLevelCount    = devLevelCount oldFocus
>                      ,  layHypState      = devHypState oldFocus
>                      }
>     putAboveCursor $ dv {devEntries = B0}
>     putBelowCursor $ NF F0
>     let deps' = case (entryDef e, occurs lev (entryName e) [] (ty :>: tm)) of 
>                    (Just d, True) -> ((d,devTip dv):deps,nest:ldeps)
>                    _ -> (deps,ldeps)
>     odnalubma' n deps' lev (ty :>: tm) (devEntries dv) (nest+1)



> tellParamEntry :: NewsBulletin -> Entry Bwd -> (Entry Bwd, NewsBulletin)
> tellParamEntry (gns, bns) (EParam k n ty l) = 
>     let (ty', ne) = tellNews (gns, bns) ty
>         bns' = case (bns, ne) of
>                  (Just bs, _)      -> Just (bs :< toBoyNews ne ty')
>                  (Nothing, NoNews) -> Nothing
>                  (Nothing, _)      -> Just (noBoyNews l :< toBoyNews ne ty')
>     in (EParam k n ty' l, (gns, bns'))

> tellTip :: Name -> NewsBulletin -> Tip ->
>            ProofState (Either (Name, TY :>: EXP) (Tip, News))
> tellTip nam news (Unknown ty Hoping) | 
>     Just (d, GoodNews) <- getGirlNews news nam = do
>   es <- getGlobalScope
>   (| (Right (Defined (defTy d :>: ((def d) $$$ paramSpine es)), GoodNews)) |)
>   -- some EInst has moved this goal out the way so solve it with the new copy
> tellTip nam news (Unknown ty hk) = (| (Right (Unknown ty' hk, ne)) |)
>   where (ty', ne) = tellNews news ty
> tellTip _ news (Defined (ty :>: tm)) = 
>     (| (Right (Defined (ty' :>: tm'), ne)) |)
>   where  (ty', ne1) = tellNews news ty
>          (tm', ne2) = tellNews news tm
>          ne         = min ne1 ne2
> tellTip _ news (SusElab ty ((nf,es), e) hk) = do
>   putDevTip (Unknown ty hk) 
>   er <- runElab (nf, map (fst . tellNews news) es) e  
>   case er of
>     ElabSuccess e' -> (| (Right (Defined (ty' :>: e'), GoodNews)) |)
>       where  (ty', _) = tellNews news ty
>     ElabWaitCan f ex c -> 
>       (| (Right (SusElab ty (f, ECan ex c) hk, NoNews)) |)
>     ElabGoInst f (n,fn) te@(ty' :>: (ex,exf)) c -> do
>       --record the progress made in the elab prob
>       putDevTip (SusElab ty'' (f, EInst (n,fn) (ty' :>: exf) c) hk)
>       (| (Left (n, ty' :>: ex)) |)
>      where  (ty'', _) = tellNews news ty
>     ElabFailed _ -> error "Tell Tip" -- run away and cry
> tellTip _ news Module = (| (Right (Module, NoNews)) |)


What fresh hell is this:

> occurs :: Int -> Maybe Name -> [Int] -> (TY :>: EXP) -> Bool 
> occurs l n p (ty :>: tm) = 
>   let tm' = etaQuote l (ty :>: tm)
>   in occurs' n p [] tm'


> occurs' :: Maybe Name -> [Int] -> [Fin {n}] -> Tm {p, s, n} -> Bool 
> occurs' Nothing [] [] _ = False
> occurs' n p v (L g x b) = let (p', v') = occursEnv n p v g in occurs' n p' (map Fs v') b
> occurs' n p v (LK b) = occurs' n p v b
> occurs' n p v (c :- es) = any (occurs' n p v) es
> occurs' n p v (f :$ as) = (occurs' n p v f) || any (any (occurs' n p v)) as
> occurs' n p v (D def) = any (defName def ==) n -- really?
> occurs' n p v (B (SIMPLDTY _ _I uDs)) = occurs' n p [] _I  || occurs' n p [] uDs 
> occurs' n p v (V i) = elem i v
> occurs' n p v (P (l , s , t)) = elem l p
> occurs' n p v (e :/ t) = let (p', v') = occursEnv n p v e in occurs' n p' v' t
> occurs' n p v (Refl _S s) = (occurs' n p v _S) || (occurs' n p v s)
> occurs' n p v (Coeh _ _S _T eq s) = 
>   (occurs' n p v _S) || (occurs' n p v _T) || (occurs' n p v eq) || (occurs' n p v s)

> occursEnv :: Maybe Name -> [Int] -> [Fin m] -> Env {m} {n} -> ([Int] , [Fin {n}]) 
> occursEnv n p v (lenv,ienv) = let (ls,os) = occursLEnv n p v lenv in
>   ((p \\ ls) `union` os, occursIEnv n p v ienv)

> occursLEnv :: Maybe Name -> [Int] -> [Fin {n}] -> LEnv {n} -> ([Int],[Int])
> occursLEnv n p v [] = ([], [])
> occursLEnv n p v ((l, t) : lenv) = 
>    let (ls, os) = occursLEnv n p v lenv 
>    in if occurs' n p v t 
>       then (l : ls, l : os)
>       else (l : ls, os) 

> occursIEnv :: Maybe Name -> [Int] -> [Fin {m}] -> IEnv {m, n} -> [Fin {n}] 
> occursIEnv n p v INix = []
> occursIEnv n p v INil = v
> occursIEnv n p v (ienv :<<: t) | occurs' n p [] t = 
>   Fz : (map Fs (occursIEnv n p v ienv)) 
> occursIEnv n p v (ienv :<<: t) = map Fs (occursIEnv n p v ienv)
