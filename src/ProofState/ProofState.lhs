%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.ProofState where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable
> import Data.List
> import Data.Traversable
> import Debug.Trace

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import ProofState.Developments

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import Evidences.Tm
> import Evidences.Rules

%endif

\section{Proof Context}

Recall from Section~\ref{sec:developments} that

< type Dev = (f (Entry f), Tip, NameSupply)

We ``unzip`` (cf. Huet's Zipper) this type to produce a type representing its
one-hole context, which allows us to keep track of the location of a working
development and perform local navigation easily.
Each |Layer| of the structure is a record with the following fields:
\begin{description}
\item[|elders|] entries appearing above the working development
\item[|mother|] data about the working development
\item[|cadets|] entries appearing below the working development
\item[|laytip|] the |Tip| of the development that contains the mother
\item[|laynsupply|] the |NameSupply| of the development that contains the mother
\end{description}

> data Layer = Layer
>   {  elders    :: Entries
>   ,  mother    :: Mother
>   ,  cadets    :: NewsyEntries
>   ,  laytip    :: Tip
>   ,  laynsupply   :: NameSupply }
>  deriving Show

> data Mother =  GirlMother REF (String, Int) INTM 
>             |  ModuleMother Name
>     deriving Show

> motherName :: Mother -> Name
> motherName (GirlMother (n := _) _ _) = n
> motherName (ModuleMother n) = n

> entryToMother :: Traversable f => Entry f -> Mother
> entryToMother (E ref xn (Girl LETG _) ty) = GirlMother ref xn ty
> entryToMother (M n _) = ModuleMother n

Because we propagate news updates lazily, we may have news bulletins below the
current cursor position, as well as entries. We defined a |newtype| for the
composition of the |Fwd| and |Either NewsBulletin| functors, and use this functor
to contain cadets.

> newtype NewsyFwd x = NF { unNF :: Fwd (Either NewsBulletin x) }

> type NewsyEntries = NewsyFwd (Entry NewsyFwd)


%if False

> instance Show (NewsyFwd (Entry NewsyFwd)) where
>     show (NF ls) = show ls

> instance Show (Entry NewsyFwd) where
>     show (E ref xn e t) = intercalate " " ["E", show ref, show xn, show e, show t]
>     show (M n d) = intercalate " " ["M", show n, show d]

> instance Show (Entity NewsyFwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

> instance Traversable NewsyFwd where
>     traverse g (NF x) = NF <$> traverse (traverse g) x

> instance Foldable NewsyFwd where
>     foldMap = foldMapDefault

> instance Functor NewsyFwd where
>     fmap = fmapDefault

%endif


When moving the cursor, we sometimes need to change the structure that
contains entries, using the following rearrangement functions.

> reverseEntry :: Entry Bwd -> Entry NewsyFwd
> reverseEntry = rearrangeEntry (NF . (fmap Right) . (<>> F0))

> reverseEntry' :: Entry Bwd -> Entry Fwd
> reverseEntry' = rearrangeEntry (<>> F0)

> reverseDev' :: Dev Bwd -> Dev Fwd
> reverseDev' = rearrangeDev (<>> F0)

> rearrangeEntry :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Entry f -> Entry g
> rearrangeEntry h (E ref xn (Boy k) ty)          = E ref xn (Boy k) ty
> rearrangeEntry h (E ref xn (Girl LETG dev) ty)  = E ref xn (Girl LETG (rearrangeDev h dev)) ty
> rearrangeEntry h (M n d)                        = M n (rearrangeDev h d)

> rearrangeEntries :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> f (Entry f) -> g (Entry g)
> rearrangeEntries h xs = h (fmap (rearrangeEntry h) xs)

> rearrangeDev :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Dev f -> Dev g
> rearrangeDev h (xs, tip, nsupply) = (rearrangeEntries h xs, tip, nsupply)


The current proof context is represented by a stack of |Layer|s, along with the
current working development (above the cursor).

> type ProofContext = (Bwd Layer, Dev Bwd)

> emptyContext :: ProofContext
> emptyContext = (B0, (B0, Module, (B0, 0)))


The |greatAuncles| function returns the elder aunts or uncles of the current development,
not including its contents.

> greatAuncles :: ProofContext -> Entries
> greatAuncles (ls, _) = foldMap elders ls

The |auncles| function returns the elder aunts or uncles of the cursor, including the
contents of the current development, thereby giving a list of entries that
are currently in scope.

> auncles :: ProofContext -> Entries
> auncles c@(_, (es, _, _)) = greatAuncles c <+> es


\section{Proof State Monad}
\label{sec:proofStateMonad}

The proof state monad provides access to the |ProofContext| as in a |State| monad,
but with the possibility of command failure represented by |Either [String]|. 

> type ProofState = StateT ProofContext (Either [String])

Handily, |Either [String]| is a |MonadPlus|, and |StateT| preserves this, so we can easily
make |ProofState| an |Alternative|:

> instance Applicative ProofState where
>     pure = return
>     (<*>) = ap

> instance Alternative ProofState where
>     empty = mzero
>     (<|>) = mplus


\subsection{Getters and Setters}

We provide various functions to get information from the proof state and store
updated information, providing a friendlier interface than |get| and |put|.

> getAuncles :: ProofState (Entries)
> getAuncles = get >>= return . auncles

> getDev :: ProofState (Dev Bwd)
> getDev = gets snd

> getDevEntries :: ProofState (Entries)
> getDevEntries = do
>     (es, _, _) <- getDev
>     return es

> getDevEntry :: ProofState (Entry Bwd)
> getDevEntry = do
>     (_ :< e, _, _) <- getDev
>     return e

> getDevNSupply :: ProofState NameSupply
> getDevNSupply = do
>     (_, _, ns) <- getDev
>     return ns

> getDevTip :: ProofState Tip
> getDevTip = do
>     (_, tip, _) <- getDev
>     return tip

> getGoal :: String -> ProofState (INTM :=>: TY)
> getGoal s = do
>     tip <- getDevTip
>     case tip of
>       Unknown (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       Defined _ (ty :=>: tyTy) -> return (ty :=>: tyTy)
>       _ -> throwError' $ "getGoal: fail to match a goal in " ++ s

> getGreatAuncles :: ProofState Entries
> getGreatAuncles = get >>= return . greatAuncles

> getBoys = do  
>     auncles <- getAuncles
>     return $ foldMap boy auncles 
>    where boy (E r _ (Boy _) _)  = [r]
>          boy _ = []

> getHoleGoal :: ProofState (INTM :=>: TY)
> getHoleGoal = do
>     GirlMother (_ := HOLE :<: _) _ _ <- getMother
>     getGoal "getHoleGoal"

> getLayer :: ProofState Layer
> getLayer = do
>     ls :< l <- getLayers
>     return l

> getLayers :: ProofState (Bwd Layer)
> getLayers = gets fst

> getMother :: ProofState Mother
> getMother = do
>     ls <- getLayers
>     case ls of
>         _ :< l  -> return (mother l)
>         B0      -> return (ModuleMother []) 

> getMotherEntry :: ProofState (Entry Bwd)
> getMotherEntry = do
>     m <- getMother
>     dev <- getDev
>     case m of
>         GirlMother ref xn ty -> return (E ref xn (Girl LETG dev) ty)
>         ModuleMother n -> return (M n dev)

> getMotherName :: ProofState Name
> getMotherName = do
>     ls <- gets fst
>     case ls of
>         (_ :< Layer{mother=m}) -> return (motherName m)
>         B0 -> return []

> insertCadet :: NewsBulletin -> ProofState ()
> insertCadet news = do
>     l <- getLayer
>     replaceLayer l{cadets = NF (Left news :> unNF (cadets l))}
>     return ()

> putDev :: Dev Bwd -> ProofState ()
> putDev dev = do
>     ls <- gets fst
>     put (ls, dev)

> putDevEntry :: Entry Bwd -> ProofState ()
> putDevEntry e = do
>     (es, tip, nsupply) <- getDev
>     putDev (es :< e, tip, nsupply)

> putDevEntries :: Entries -> ProofState ()
> putDevEntries es = do
>     (_, tip, nsupply) <- getDev
>     putDev (es, tip, nsupply)

> putDevNSupply :: NameSupply -> ProofState ()
> putDevNSupply ns = do
>     (es, tip, _) <- getDev
>     putDev (es, tip, ns)

> putDevTip :: Tip -> ProofState ()
> putDevTip tip = do
>     (es, _, r) <- getDev
>     putDev (es, tip, r)

> putLayer :: Layer -> ProofState ()
> putLayer l = do
>     (ls, dev) <- get
>     put (ls :< l, dev)

> putMother :: Mother -> ProofState ()
> putMother m = do
>     l <- getLayer
>     _ <- replaceLayer l{mother=m}
>     return ()

> putMotherEntry :: Entry Bwd -> ProofState ()
> putMotherEntry (E ref xn (Girl LETG dev) ty) = do
>     l <- getLayer
>     replaceLayer (l{mother=GirlMother ref xn ty})
>     putDev dev
> putMotherEntry (M [] dev) = putDev dev
> putMotherEntry (M n dev) = do
>     l <- getLayer
>     replaceLayer (l{mother=ModuleMother n})
>     putDev dev

> removeDevEntry :: ProofState (Maybe (Entry Bwd))
> removeDevEntry = do
>     es <- getDevEntries
>     case es of
>       B0 -> return Nothing
>       (es' :< e) -> do
>         putDevEntries es'
>         return (Just e)

> removeLayer :: ProofState Layer
> removeLayer = do
>     (ls :< l, dev) <- get
>     put (ls, dev)
>     return l

> replaceDev :: Dev Bwd -> ProofState (Dev Bwd)
> replaceDev dev = do
>     (ls, dev') <- get
>     put (ls, dev)
>     return dev'

> replaceDevEntries :: Entries -> ProofState Entries
> replaceDevEntries es = do
>     es' <- getDevEntries
>     putDevEntries es
>     return es'

> replaceLayer :: Layer -> ProofState Layer
> replaceLayer l = do
>     (ls :< l', dev) <- get
>     put (ls :< l, dev)
>     return l'


\subsection{Proof State Technology}

A |ProofState| is not a |NameSupplier| because the semantics of the latter are not compatible
with the caching of |NameSupply|s in the proof context. However, it can provide the current
|NameSupply| to a function that requires it. Note that this function has no way to return
an updated name supply to the proof context, so it must not leave any references around
when it has finished.

> withNSupply :: (NameSupply -> x) -> ProofState x
> withNSupply f = getDevNSupply >>= return . f


The |bquoteHere| command $\beta$-quotes a term using the current name supply.

> bquoteHere :: Tm {d, VV} REF -> ProofState (Tm {d, TT} REF)
> bquoteHere tm = withNSupply (bquote B0 tm)


> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere (ty :>: tm) = do
>     mc <- withNSupply (typeCheck $ check (ty :>: tm))
>     () :=>: tmv <- lift mc
>     return (tm :=>: tmv)



The |resolveHere| command resolves the relative names in a term.

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

> lookupName :: Name -> ProofState INTM
> lookupName name = do
>   aus <- getAuncles
>   let Just (E ref _ _ _) = Data.Foldable.find ((name ==) . entryName) aus
>   return $ (N (P ref $:$ aunclesToElims (aus <>> F0)))

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
>             Right e -> case coerceEntry e of
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
>             return (N (P ref $:$ aunclesToElims (aus <>> F0)))
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
>     s' <- pickName s
>     n <- withNSupply (flip mkName s')
>     let  ty'  = liftType aus ty
>          ref  = n := HOLE :<: evTm ty'
>     nsupply <- getDevNSupply
>     putDevEntry (E ref (last n) (Girl LETG (B0, Unknown (ty :=>: tyv), freshNSpace nsupply s')) ty')
>     putDevNSupply (freshName nsupply)
>     return (N (P ref $:$ aunclesToElims (aus <>> F0)))

> aunclesToElims :: Fwd (Entry Bwd) -> [Elim INTM]
> aunclesToElims F0 = []
> aunclesToElims (E ref _ (Boy _) _ :> es) = (A (N (P ref))) : aunclesToElims es
> aunclesToElims (_ :> es) = aunclesToElims es


> makeModule :: String -> ProofState Name
> makeModule s = do
>     n <- withNSupply (flip mkName s)
>     nsupply <- getDevNSupply
>     putDevEntry (M n (B0, Module, freshNSpace nsupply s))
>     putDevNSupply (freshName nsupply)
>     return n

> pickName :: String -> ProofState String
> pickName ""  = do
>     r <- getDevNSupply
>     return ("G" ++ show (snd r))
> pickName s   = return s


> moduleToGoal :: INTM -> ProofState INTM
> moduleToGoal ty = do
>     Right (() :=>: tyv) <- withNSupply (typeCheck $ check (SET :>: ty))
>     ModuleMother n <- getMother
>     aus <- getAuncles
>     let  ty' = liftType aus ty
>          ref = n := HOLE :<: evTm ty'
>     putMother (GirlMother ref (last n) ty')
>     putDevTip (Unknown (ty :=>: tyv))
>     return (N (P ref $:$ aunclesToElims (aus <>> F0)))

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



\section{Wire Service}

Here we describe how to handle updates to references in the proof state, caused by
refinement commands like |give|. The idea is to deal with updates lazily, to avoid
unnecessary traversals of the proof tree. When |updateRef| is called to announce
a changed reference (that the current development has already processed), it simply
inserts a news bulletin below the current development.

> updateRef :: REF -> ProofState ()
> updateRef ref = insertCadet [(ref, GoodNews)]


The |propagateNews| function takes a current news bulletin and a list of entries
to add to the current development. It applies the news bulletin to each entry
in turn, picking up other bulletins along the way. This function should be called
when navigating to a development that may contain news bulletins, so they can be
pushed out of sight.

> propagateNews :: Bool -> NewsBulletin -> NewsyEntries -> ProofState NewsBulletin

If we have nothing to say and nobody to tell, we might as well give up and go home.

> propagateNews _ [] (NF F0) = return []

> propagateNews False news (NF F0) = return news

If there are no entries to process, we should tell the mother (if there is one),
stash the bulletin after the current location and stop. Note that the insertion is
optional because it will fail when we have reached the end of the module, at which
point everyone knows the news anyway.

> propagateNews True news (NF F0) = do
>     news' <- tellMother news
>     optional (insertCadet news')
>     return news'

A |Boy| is relatively easy to deal with, we just check to see if its type
has become more defined, and pass on the good news if necessary.

> propagateNews top news (NF (Right (E (name := DECL :<: tv) sn (Boy k) ty) :> es)) = do
>     case tellNews news ty of
>         (_, NoNews) -> putDevEntry (E (name := DECL :<: tv) sn (Boy k) ty) >> propagateNews top news (NF es)
>         (ty', GoodNews) -> do
>             let ref = name := DECL :<: evTm ty'
>             putDevEntry (E ref sn (Boy k) ty')
>             propagateNews top (addNews (ref, GoodNews) news) (NF es)

Updating girls is a bit more complicated. We proceed as follows:
\begin{enumerate}
\item Add the girl to the context, using |jumpIn|.
\item Recursively propagate the news to the children.
\item Call |tellMother| to update the girl herself.
\item Continue propagating the latest news.
\end{enumerate}

> propagateNews top news (NF ((Right e@(E ref sn (Girl LETG (_, tip, nsupply)) ty)) :> es)) = do
>     xs <- jumpIn e
>     news' <- propagateNews False news xs
>     news'' <- tellMother news'
>     goOut
>     propagateNews top news'' (NF es)

Modules do not carry type information so all we need to do is propagate
the news to their children.

> propagateNews top news (NF (Right e@(M n d) :> es)) = do
>     xs <- jumpIn e
>     news' <- propagateNews False news xs
>     goOut
>     propagateNews top news (NF es)


Finally, if we encounter an older news bulletin when propagating news, we can simply
merge the two together.

> propagateNews top news (NF (Left oldNews :> es)) =
>   propagateNews top (mergeNews news oldNews) (NF es)


The |tellEntry| function informs an entry about a news bulletin that its
children have already received. If the entry is a girl, she must be the
mother of the current cursor position (i.e. the entry should come from
getMotherEntry).

> tellEntry :: NewsBulletin -> Entry Bwd -> ProofState (NewsBulletin, Entry Bwd)

Modules carry no type information, so they are easy:

> tellEntry news (M n d) = return (news, M n d)

To update a boy, we must:
\begin{enumerate}
\item update the overall type of the entry, and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellEntry news (E (name := DECL :<: tv) sn (Boy k) ty) = do
>     let (ty' :=>: tv', n)  = tellNewsEval news (ty :=>: tv)
>     let ref = name := DECL :<: tv'
>     return (addNews (ref, n) news, E ref sn (Boy k) ty')

To update a hole, we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference; and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellEntry news (E (name := HOLE :<: tyv) sn (Girl LETG (cs, Unknown tt, nsupply)) ty) = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          ref                  = name := HOLE :<: tyv'
>     return (addNews (ref, min n n') news,
>                 E ref sn (Girl LETG (cs, Unknown tt', nsupply)) ty')

To update a defined girl, we must:
\begin{enumerate}
\item update the tip type;
\item update the overall type of the entry, as stored in the reference;
\item update the definition and re-evaluate it
         (\question{could this be made more efficient?}); and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellEntry news (E (name := DEFN tmL :<: tyv) sn (Girl LETG (cs, Defined tm tt, nsupply)) ty) = do
>     let  (tt', n)             = tellNewsEval news tt
>          (ty' :=>: tyv', n')  = tellNewsEval news (ty :=>: tyv)
>          (tm', n'')           = tellNews news tm
>     aus <- getGreatAuncles
>     let tmL' = parBind aus cs tm'

For paranoia purposes, the following test might be helpful:

<     mc <- withNSupply (inCheck $ check (tyv' :>: tmL'))
<     mc `catchEither` unlines ["tellEntry " ++ showName name ++ ":",
<                                 show tmL', "is not of type", show ty' ]

>     let ref = name := DEFN (evTm tmL') :<: tyv'
>     return (addNews (ref, GoodNews {-min (min n n') n''-}) news,
>                 E ref sn (Girl LETG (cs, Defined tm' tt', nsupply)) ty')


> proofTrace :: String -> ProofState ()
> proofTrace s = do
>   () <- trace s $ return ()
>   return ()


The |tellMother| function informs the mother entry about a news bulletin
that her children have already received, and returns the updated news.

> tellMother :: NewsBulletin -> ProofState NewsBulletin
> tellMother news = do
>     e <- getMotherEntry
>     (news', e') <- tellEntry news e 
>     putMotherEntry e'
>     return news'


The |tellNews| function applies a bulletin to a term. It returns the updated
term and the news about it.

> tellNews :: NewsBulletin -> Tm {d, TT} REF -> (Tm {d, TT} REF, News)
> tellNews []    tm = (tm, NoNews)
> tellNews news  tm = case foldMap (lookupNews news) tm of
>     NoNews  -> (tm, NoNews)
>     n       -> (fmap (getLatest news) tm, n)

The |tellNewsEval| function takes a bulletin, term and its present value.
It updates the term with the bulletin and re-evaluates it if necessary.

> tellNewsEval :: NewsBulletin -> INTM :=>: VAL -> (INTM :=>: VAL, News)
> tellNewsEval news (tm :=>: tv) = case tellNews news tm of
>     (_,    NoNews)    -> (tm   :=>: tv,        NoNews)
>     (tm',  GoodNews)  -> (tm'  :=>: evTm tm',  GoodNews)
