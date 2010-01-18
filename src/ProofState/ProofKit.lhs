\section{The |ProofState| Kit}
\label{sec:proof_state_kit}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.ProofKit where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable
> import Data.List

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import ProofState.Developments
> import ProofState.News
> import ProofState.Lifting
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.Wire

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import Evidences.Tm
> import Evidences.Rules

%endif

\question{There are some serious re-ordering of functions to be done
here, in order to improve the narrative.}


\subsection{Asking for Evidences}


A |ProofState| is not a |NameSupplier| because the semantics of the
latter are not compatible with the caching of |NameSupply|s in the
proof context. However, it can provide the current |NameSupply| to a
function that requires it. 

> withNSupply :: (NameSupply -> x) -> ProofState x
> withNSupply f = getDevNSupply >>= return . f

\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


The |bquoteHere| command $\beta$-quotes a term using the current name supply.

> bquoteHere :: Tm {d, VV} REF -> ProofState (Tm {d, TT} REF)
> bquoteHere tm = withNSupply $ bquote B0 tm


Similarly, |checkHere| type-checks a term using the local name supply.

> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere (ty :>: tm) = do
>     mc <- withNSupply $ typeCheck $ check (ty :>: tm)
>     () :=>: tmv <- lift mc
>     return (tm :=>: tmv)


The |resolveHere| command resolves the relative names in a term. This
is not quite an evidence, but we are one step closer.

> resolveHere :: InDTmRN -> ProofState INDTM
> resolveHere tm = do
>     aus <- getAuncles
>     resolve aus tm `catchEither` "resolveHere: could not resolve names in term"


The |validateHere| performs some checks on the current location, which
may be useful for paranoia purposes.

> validateHere :: ProofState ()
> validateHere = do
>     m <- getMother
>     case m of
>         GirlMother (_ := DEFN tm :<: ty) _ _ -> do
>             ty' <- bquoteHere ty
>             mc <- withNSupply (typeCheck $ check (SET :>: ty'))
>             mc `catchEither` intercalate "\n" ["validateHere: girl type failed to type-check: SET does not admit", show ty']
>             tm' <- bquoteHere tm
>             mc <- withNSupply (typeCheck $ check (ty :>: tm'))
>             mc `catchEither` intercalate "\n" ["validateHere: definition failed to type-check:", show ty, "does not admit", show tm']
>             return ()
>         _ -> return ()



\subsection{Navigation Commands}


Now we provide commands to navigate the proof state:
\begin{itemize}
\item |goIn| changes the current location to the bottom-most girl in the current development;
\item |goOut| goes up a layer, so the focus changes to the development containing
the current working location;
\item |goUp| moves the focus to the next eldest girl;
\item |goDown| moves the focus to the next youngest girl.
\end{itemize}

These commands fail (yielding |Nothing|) if they are impossible because the proof context
is not in the required form.

> goIn :: ProofState ()
> goIn = goInAcc (NF F0) `replaceError` "goIn: you can't go that way."
>   where
>     goInAcc :: NewsyEntries -> ProofState ()
>     goInAcc (NF cadets) = do
>         (ls, (es :< e, tip, nsupply)) <- get
>         if entryHasDev e
>            then  put (ls :< Layer es (entryToMother e) (NF cadets) tip nsupply, entryDev e)
>            else  put (ls, (es, tip, nsupply))
>                  >> goInAcc (NF (Right (reverseEntry e) :> cadets)) 


> jumpIn :: Entry NewsyFwd -> ProofState NewsyEntries
> jumpIn e = do
>     (ls, (es, tip, nsupply)) <- get
>     let (cs, newTip, newNSupply) = entryDev e
>     put (ls :< Layer es (entryToMother e) (NF F0) tip nsupply, (B0, newTip, newNSupply))
>     return cs

> goOut :: ProofState ()
> goOut = (do
>     e <- getMotherEntry
>     l <- removeLayer
>     putDev (elders l :< e, laytip l, laynsupply l)
>     propagateNews True [] (cadets l)  -- should update tip and pass on news
>     return ()
>   ) `replaceError` "goOut: you can't go that way."

> goUp :: ProofState ()
> goUp = goUpAcc (NF F0) `replaceError` "goUp: you can't go that way."
>   where
>     goUpAcc :: NewsyEntries -> ProofState ()
>     goUpAcc (NF acc) = do
>         l@(Layer (es :< e) m (NF cadets) tip nsupply) <- getLayer
>         if entryHasDev e
>             then do
>                 me <- getMotherEntry
>                 putDev (entryDev e)
>                 replaceLayer l{elders=es, mother=entryToMother e, cadets=NF (acc <+> 
>                     (Right (reverseEntry me) :> cadets))}
>                 return ()
>             else  replaceLayer l{elders=es}
>                   >> goUpAcc (NF (Right (reverseEntry e) :> acc))

> goDown :: ProofState ()
> goDown = goDownAcc B0 [] `replaceError` "goDown: you can't go that way."
>   where
>     goDownAcc :: Entries -> NewsBulletin -> ProofState ()
>     goDownAcc acc news = do
>         l@(Layer elders _ (NF (ne :> es)) _ _) <- getLayer
>         case ne of
>             Left nb -> do
>                 replaceLayer l{cadets=NF es}
>                 goDownAcc acc (mergeNews news nb)
>             Right e -> case entryCoerce e of
>               Left (es', tip', nsupply') ->  do
>                 me <- getMotherEntry
>                 replaceLayer l{elders=(elders :< me) <+> acc, mother=entryToMother e, cadets=NF es}
>                 putDev (B0, tip', nsupply')
>                 news' <- propagateNews True news es'
>                 return ()
>               Right e' -> do
>                 (news', e'') <- tellEntry news e'
>                 replaceLayer l{cadets=NF es}
>                 goDownAcc (acc :< e'') news'

> goTo :: Name -> ProofState ()
> goTo [] = return ()
> goTo (xn:xns) = (seek xn >> goTo xns)
>     `replaceError` ("goTo: could not find " ++ showName (xn:xns))
>   where
>     seek :: (String, Int) -> ProofState ()
>     seek xn = (goUp <|> goIn) >> do
>         m <- getMotherName
>         if xn == last m
>             then return ()
>             else removeDevEntry >> seek xn


\subsection{Goal Search Commands}

To implement goal search, we need a few useful bits of kit...

The |untilA| operator runs its first argument one or more times until its second
argument succeeds, at which point it returns the result. If the first argument
fails, the whole operation fails.

> untilA :: Alternative f => f () -> f a -> f a
> g `untilA` test = g *> try
>     where try = test <|> (g *> try)

The |much| operator runs its argument until it fails, then returns the state of
its last success. It is very similar to |many|, except that it throws away the
results.

> much :: Alternative f => f () -> f ()
> much f = (f *> much f) <|> pure ()

The |isGoal| command succeeds (returning |()|) if the current location is a goal,
and fails (yielding |Nothing|) if not.

> isGoal :: ProofState ()
> isGoal = do
>     Unknown _ <- getDevTip
>     return ()


We can now compactly describe how to search the proof state for goals, by giving
several alternatives for where to go next and continuing until a goal is reached.

> prevStep :: ProofState ()
> prevStep = ((goUp >> much goIn) <|> goOut) `replaceError` "prevStep: no previous steps."
>
> prevGoal :: ProofState ()
> prevGoal = (prevStep `untilA` isGoal) `replaceError` "prevGoal: no previous goals."
>
> nextStep :: ProofState ()
> nextStep = ((goIn >> much goUp) <|> goDown <|> (goOut `untilA` goDown))
>                `replaceError` "nextStep: no more steps."
>
> nextGoal :: ProofState ()
> nextGoal = (nextStep `untilA` isGoal) `replaceError` "nextGoal: no more goals."



\subsection{Module Commands}


> makeModule :: String -> ProofState Name
> makeModule s = do
>     n <- withNSupply (flip mkName s)
>     nsupply <- getDevNSupply
>     putDevEntry (M n (B0, Module, freshNSpace nsupply s))
>     putDevNSupply (freshName nsupply)
>     return n

> moduleToGoal :: INTM -> ProofState INTM
> moduleToGoal ty = do
>     Right (() :=>: tyv) <- withNSupply (typeCheck $ check (SET :>: ty))
>     ModuleMother n <- getMother
>     aus <- getAuncles
>     let  ty' = liftType aus ty
>          ref = n := HOLE :<: evTm ty'
>     putMother (GirlMother ref (last n) ty')
>     putDevTip (Unknown (ty :=>: tyv))
>     return (applyAuncles ref aus)

> dropModule :: ProofState ()
> dropModule = do
>     Just (M _ _) <- removeDevEntry
>     return ()

> draftModule :: String -> ProofState t -> ProofState t
> draftModule name draftyStuff = do
>     makeModule name
>     goIn
>     t <- draftyStuff
>     goOut
>     dropModule
>     return t


The |lookupName| function looks up a name in the context (including axioms and
primitives); if found, it returns the reference applied to the spine of
shared parameters.

> lookupName :: Name -> ProofState (Maybe INTM)
> lookupName name = do
>     aus <- getAuncles
>     case Data.Foldable.find ((name ==) . entryName) aus of
>       Just (E ref _ _ _)  -> return (Just (applyAuncles ref aus))
>       Nothing             ->
>         case Data.Foldable.find ((name ==) . refName . snd) (axioms ++ primitives) of
>           Just (_, ref)  -> return (Just (applyAuncles ref aus))
>           Nothing        -> return Nothing



\subsection{Construction Commands}

The |apply| command checks if the last entry in the development is a girl $y$ with type
$\Pi S T$ and if so, adds a goal of type $S$ and applies $y$ to it.

> apply :: ProofState()
> apply = (do
>     E ref@(name := k :<: (PI s t)) _ (Girl LETG _) _ <- getDevEntry
>     nsupply <- getDevNSupply
>     z <- make ("z" :<: bquote B0 s nsupply)
>     make ("w" :<: bquote B0 (t $$ A s) nsupply)
>     goIn
>     give (N (P ref :$ A z))
>     return ()
>   ) `replacePMF` "apply: last entry in the development must be a girl with a pi-type."

The |done| command checks if the last entry in the development is a girl, and if so,
fills in the goal with this entry.

> done :: ProofState INTM
> done = (do
>     E ref _ (Girl LETG _) _ <- getDevEntry
>     give (N (P ref))
>  ) `replacePMF` "done: last entry in the development must be a girl."

The |give| command checks the provided term has the goal type, and if so, fills in
the goal, updates the reference and goes out. The |giveNext| variant moves to the
next goal (if one exists) instead.

> give :: INTM -> ProofState INTM
> give tm = give' tm <* goOut

> giveNext :: INTM -> ProofState INTM
> giveNext tm = give' tm <* (nextGoal <|> goOut)

> give' :: INTM -> ProofState INTM
> give' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             mc <- withNSupply (typeCheck $ check (tipTy :>: tm))
>             mc `catchEither` intercalate "\n" [ "Typechecking failed:"
>                                              , show tm
>                                              , "is not of type"
>                                              , show tipTyTm ]
>             aus <- getGreatAuncles
>             sibs <- getDevEntries
>             let tmv = evTm (parBind aus sibs tm)
>             GirlMother (name := _ :<: tyv) xn ty <- getMother
>             let ref = name := DEFN tmv :<: tyv
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             putMother (GirlMother ref xn ty)
>             updateRef ref
>             return (applyAuncles ref aus)
>         _  -> throwError' "give: only possible for incomplete goals."

The |lambdaBoy| command checks that the current goal is a $\Pi$-type, and if so,
appends a $\lambda$-abstraction with the appropriate type to the current development.

> lambdaBoy :: String -> ProofState REF
> lambdaBoy x = do
>     tip <- getDevTip
>     case tip of
>       Unknown (pi :=>: ty) -> case lambdable ty of
>         Just (k, s, t) -> do
>           nsupply <- getDevNSupply
>           freshRef (x :<: s) (\ref r -> do
>             putDevEntry (E ref (lastName ref) (Boy k) (bquote B0 s r))
>             let tipTyv = t (pval ref)
>             putDevTip (Unknown (bquote B0 tipTyv r :=>: tipTyv))
>             putDevNSupply r
>             return ref
>               ) nsupply
>         _  -> throwError' "lambdaBoy: goal is not a pi-type or all-proof."
>       _          -> throwError' "lambdaBoy: only possible for incomplete goals."

The following piece of kit might profitably be shifted to somewhere more
general.

> lambdable :: TY -> Maybe (BoyKind, TY, VAL -> TY)
> lambdable (PI s t)         = Just (LAMB, s, (t $$) . A)
> lambdable (PRF (ALL s p))  = Just (ALAB, s, \v -> PRF (p $$ A v))
> lambdable _                = Nothing

> lambdaBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> lambdaBoy' (x :<: (ty :=>: tv))  = do
>     tip <- getDevTip
>     case tip of
>       Module -> do
>         nsupply <- getDevNSupply
>         freshRef (x :<: tv) (\ref r -> do
>           putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>           putDevNSupply r
>           return ref
>             ) nsupply
>       Unknown (pi :=>: gty) -> case lambdable gty of
>         Just (k, s, t) -> do
>           nsupply <- getDevNSupply
>           case equal (SET :>: (tv,s)) nsupply of
>             True -> do 
>               freshRef (x :<: tv) (\ref r -> do
>               putDevEntry (E ref (lastName ref) (Boy k) ty)
>               let tipTyv = t (pval ref)
>               putDevTip (Unknown (bquote B0 tipTyv r :=>: tipTyv))
>               putDevNSupply r
>               return ref) nsupply
>             False -> throwError' "Given type does not match domain of goal"
>         _  -> throwError' "lambdaBoy: goal is not a pi-type or all-proof."
>       _ -> throwError' "lambdaBoy: only possible at Tips"


The |make| command adds a named goal of the given type to the bottom of the
current development, after checking that the purported type is in fact a type.

> make :: (String :<: INTM) -> ProofState INTM
> make (s :<: ty) = do
>     m <- withNSupply (typeCheck $ check (SET :>: ty))
>     m `catchEither` ("make: " ++ show ty ++ " is not a set.")
>     make' (s :<: (ty :=>: evTm ty))

> make' :: (String :<: (INTM :=>: TY)) -> ProofState INTM
> make' (s :<: (ty :=>: tyv)) = do
>     aus <- getAuncles
>     s' <- pickName "G" s
>     n <- withNSupply (flip mkName s')
>     let  ty'  = liftType aus ty
>          ref  = n := HOLE :<: evTm ty'
>     nsupply <- getDevNSupply
>     putDevEntry (E ref (last n) (Girl LETG (B0, Unknown (ty :=>: tyv), freshNSpace nsupply s')) ty')
>     putDevNSupply (freshName nsupply)
>     return (applyAuncles ref aus)


The |applyAuncles| command applies a reference to the given
spine of shared parameters.

> applyAuncles :: REF -> Entries -> INTM
> applyAuncles ref aus = N (P ref $:$ aunclesToElims (aus <>> F0))

> aunclesToElims :: Fwd (Entry Bwd) -> [Elim INTM]
> aunclesToElims F0 = []
> aunclesToElims (E ref _ (Boy _) _ :> es) = (A (N (P ref))) : aunclesToElims es
> aunclesToElims (_ :> es) = aunclesToElims es


The |pickName| command takes a prefix suggestion and a name suggestion
(either of which may be empty), and returns a more-likely-to-be-unique
name if the name suggestion is empty.

> pickName :: String -> String -> ProofState String
> pickName "" s = pickName "x" s
> pickName prefix ""  = do
>     m <- getMotherName
>     r <- getDevNSupply
>     return (prefix ++ foldMap (show . snd) m ++ show (snd r))
> pickName _ s   = return s


The |piBoy| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piBoy :: (String :<: INTM) -> ProofState REF
> piBoy (s :<: ty) = piBoy' (s :<: (ty :=>: evTm ty))

> piBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> piBoy' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> do
>             nsupply <- getDevNSupply
>             freshRef (s :<: tv)
>                 (\ref r ->  do
>                    putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>                    putDevNSupply r
>                    return ref) nsupply
>         Unknown _  -> throwError' "piBoy: goal is not of type SET."
>         _          -> throwError' "piBoy: only possible for incomplete goals."

The |select| command takes a term representing a neutral parameter, makes a new goal of the
same type, and fills it in with the parameter. \question{Is bquote really right here?}

> select :: INTM -> ProofState INTM
> select tm@(N (P (name := k :<: ty))) = do
>     nsupply <- getDevNSupply
>     make (fst (last name) :<: bquote B0 ty nsupply)
>     goIn
>     give tm
> select _ = throwError' "select: term is not a parameter."
     
The |ungawa| command looks for a truly obvious thing to do, and does it.

> ignore :: ProofState a -> ProofState ()
> ignore f = do
>     f
>     return ()

> ungawa :: ProofState ()
> ungawa = (ignore done <|> ignore apply <|> ignore (lambdaBoy "ug"))
>     `replaceError` "ungawa: no can do."



\subsection{Information Commands}

> infoAuncles :: ProofState String
> infoAuncles = do
>     aus <- getAuncles
>     me <- getMotherName
>     return (showEntries aus me (aus <>> F0))

> infoDump :: ProofState String
> infoDump = do
>     (es, dev) <- get
>     return (foldMap ((++ "\n") . show) es ++ show dev)
