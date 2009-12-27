%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances, GADTs #-}

> module ProofState where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import BwdFwd
> import Developments
> import Naming
> import PrettyPrint
> import Root
> import Rooty
> import Rules
> import Tm
> import MissingLibrary

%endif

\section{Proof Context}

Recall from Section~\ref{sec:developments} that

< type Dev = (f (Entry f), Tip, Root)

We ``unzip`` (cf. Huet's Zipper) this type to produce a type representing its
one-hole context, which allows us to keep track of the location of a working
development and perform local navigation easily.
Each |Layer| of the structure is a record with the following fields:
\begin{description}
\item[|elders|] entries appearing above the working development
\item[|mother|] the |REF| of the |Entry| that contains the working development
\item[|motherTy|] the term representation of the type of |mother|
\item[|cadets|] entries appearing below the working development
\item[|laytip|] the |Tip| of the containing development
\item[|layroot|] the |Root| of the containing development
\end{description}

> data Layer = Layer
>   {  elders    :: Entries
>   ,  mother    :: Mother
>   ,  cadets    :: NewsyEntries
>   ,  laytip    :: Tip
>   ,  layroot   :: Root }
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


When moving the cursor backwards, we sometimes need to reverse the direction of contained
entries, using the |reverseEntry|, |reverseEntries| and |reverseDev| functions.

> reverseEntry :: Entry Bwd -> Entry NewsyFwd
> reverseEntry (E ref xn (Boy k) ty)          = E ref xn (Boy k) ty
> reverseEntry (E ref xn (Girl LETG dev) ty)  = E ref xn (Girl LETG (reverseDev dev)) ty
> reverseEntry (M n d)                        = M n (reverseDev d)

> reverseEntries :: Entries -> NewsyEntries
> reverseEntries xs = NF (fmap (Right . reverseEntry) xs <>> F0)

> reverseDev :: Dev Bwd -> Dev NewsyFwd
> reverseDev (xs, tip, root) = (reverseEntries xs, tip, root)


> reverseEntry' :: Entry Bwd -> Entry Fwd
> reverseEntry' (E ref xn (Boy k) ty)          = E ref xn (Boy k) ty
> reverseEntry' (E ref xn (Girl LETG dev) ty)  = E ref xn (Girl LETG (reverseDev' dev)) ty
> reverseEntry' (M n d)                        = M n (reverseDev' d)

> reverseEntries' :: Entries -> Fwd (Entry Fwd)
> reverseEntries' xs = fmap reverseEntry' xs <>> F0

> reverseDev' :: Dev Bwd -> Dev Fwd
> reverseDev' (xs, tip, root) = (reverseEntries' xs, tip, root)



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

> getDevRoot :: ProofState Root
> getDevRoot = do
>     (_, _, root) <- getDev
>     return root

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
>     l <- getLayer
>     dev <- getDev
>     case mother l of
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
>     (es, tip, root) <- getDev
>     putDev (es :< e, tip, root)

> putDevEntries :: Entries -> ProofState ()
> putDevEntries es = do
>     (_, tip, root) <- getDev
>     putDev (es, tip, root)

> putDevRoot :: Root -> ProofState ()
> putDevRoot r = do
>     (es, tip, _) <- getDev
>     putDev (es, tip, r)

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

A |ProofState| is not |Rooty| because the semantics of the latter are not compatible
with the caching of |Root|s in the proof context. However, it can provide the current
|Root| to a function that requires it. Note that this function has no way to return
an updated root to the proof context, so it must not leave any references around
when it has finished.

> withRoot :: (Root -> x) -> ProofState x
> withRoot f = getDevRoot >>= return . f


The |bquoteHere| command $\beta$-quotes a term using the current root.

> bquoteHere :: Tm {d, VV} REF -> ProofState (Tm {d, TT} REF)
> bquoteHere tm = withRoot (bquote B0 tm)


The |prettyHere| command christens a term in the current context, then passes it
to the pretty-printer.

> prettyHere :: INTM -> ProofState String
> prettyHere tm = do
>     aus <- getAuncles
>     me <- getMotherName
>     return (show (pretty (christen aus me tm)))


The |resolveHere| command resolves the relative names in a term.

> resolveHere :: InTmRN -> ProofState INTM
> resolveHere tm = do
>     aus <- getAuncles
>     resolve aus tm `catchMaybe` "resolveHere: could not resolve names in term"


> prettyProofState :: ProofState String
> prettyProofState = do
>     me <- getMotherName
>     gaus <- getGreatAuncles
>     ls <- gets fst
>     dev <- getDev
>     case ls of
>         B0      -> return (show (prettyModule gaus me dev))
>         _ :< _  -> return (show (prettyDev gaus me dev))


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
>         (ls, (es :< e, tip, root)) <- get
>         if entryHasDev e
>            then  put (ls :< Layer es (entryToMother e) (NF cadets) tip root, entryDev e)
>            else  put (ls, (es, tip, root))
>                  >> goInAcc (NF (Right (reverseEntry e) :> cadets)) 


> jumpIn :: Entry NewsyFwd -> ProofState NewsyEntries
> jumpIn e = do
>     (ls, (es, tip, root)) <- get
>     let (cs, newTip, newRoot) = entryDev e
>     put (ls :< Layer es (entryToMother e) (NF F0) tip root, (B0, newTip, newRoot))
>     return cs

> goOut :: ProofState ()
> goOut = (do
>     e <- getMotherEntry
>     l <- removeLayer
>     putDev (elders l :< e, laytip l, layroot l)
>     propagateNews [] (cadets l)
>     return ()
>   ) `replaceError` "goOut: you can't go that way."

> goUp :: ProofState ()
> goUp = goUpAcc (NF F0) `replaceError` "goUp: you can't go that way."
>   where
>     goUpAcc :: NewsyEntries -> ProofState ()
>     goUpAcc (NF acc) = do
>         l@(Layer (es :< e) m (NF cadets) tip root) <- getLayer
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
>         l@(Layer elders _ (NF (e :> es)) _ _) <- getLayer
>         case e of
>             Left nb -> do
>                 replaceLayer l{cadets=NF es}
>                 goDownAcc acc (mergeNews news nb)
>             Right e' -> if entryHasDev e'
>               then do
>                 me <- getMotherEntry
>                 let (NF es', tip', root') = entryDev e'
>                 oldDev <- replaceDev (B0, tip', root')
>                 news' <- propagateNews news (NF es')
>                 dev <- getDev
>                 let e'' = replaceEntryDev e' dev
>                 (news'', e''') <- tellEntry news' e''
>                 replaceDev (entryDev e''')
>                 replaceLayer  l{elders=(elders :< me) <+> acc,
>                               mother=entryToMother e''', cadets=NF (Left news'' :> es)}
>                 return ()
>               else do
>                 replaceLayer l{cadets=NF es}
>                 goDownAcc (acc :< coerceEntry e') news

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
>     root <- getDevRoot
>     z <- make ("z" :<: bquote B0 s root)
>     make ("w" :<: bquote B0 (t $$ A s) root)
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
the goal and updates the reference.

> give :: INTM -> ProofState INTM
> give tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             mc <- withRoot (check (tipTy :>: tm))
>             aus <- getGreatAuncles
>             sibs <- getDevEntries
>             let tmv = evTm (parBind aus sibs tm)
>             GirlMother (name := _ :<: tyv) xn ty <- getMother
>             let ref = name := DEFN tmv :<: tyv
>             prettyTm <- prettyHere tm
>             prettyTipTyTm <- prettyHere tipTyTm
>             mc `catchMaybe` intercalate "\n" [ "Typechecking failed:"
>                                              , prettyTm
>                                              , "is not of type"
>                                              , prettyTipTyTm ]
>             putMother (GirlMother ref xn ty)
>             updateRef ref
>             goOut
>             return (N (P ref $:$ aunclesToElims (aus <>> F0)))
>         _  -> throwError' "give: only possible for incomplete goals."

> giveSilently :: INTM -> ProofState ()
> giveSilently tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             aus <- getGreatAuncles
>             sibs <- getDevEntries
>             let tmv = evTm (parBind aus sibs tm)
>             GirlMother (name := _ :<: tyv) xn ty <- getMother
>             let ref = name := DEFN tmv :<: tyv
>             putMother (GirlMother ref xn ty)
>             goOut
>         _  -> throwError' "give: only possible for incomplete goals."

The |lambdaBoy| command checks that the current goal is a $\Pi$-type, and if so,
appends a $\lambda$-abstraction with the appropriate type to the current development.

> lambdaBoy :: String -> ProofState REF
> lambdaBoy x = do
>     tip <- getDevTip
>     case tip of
>         Unknown (pi :=>: PI s t) -> do
>             root <- getDevRoot
>             (Root.freshRef (x :<: s) (\ref r -> do
>                 putDevEntry (E ref (lastName ref) (Boy LAMB) (bquote B0 s r))
>                 let tipTyv = t $$ A (pval ref)
>                 putDevTip (Unknown (bquote B0 tipTyv r :=>: tipTyv))
>                 putDevRoot r
>                 return ref
>               ) root)
>         Unknown _  -> throwError' "lambdaBoy: goal is not a pi-type."
>         _          -> throwError' "lambdaBoy: only possible for incomplete goals."

The |make| command adds a named goal of the given type to the bottom of the
current development, after checking that the purported type is in fact a type.

> make :: (String :<: INTM) -> ProofState INTM
> make (s :<: ty) = do
>     m <- withRoot (check (SET :>: ty))
>     m `catchMaybe` ("make: " ++ show ty ++ " is not a set.")
>     make' (s :<: (ty :=>: evTm ty))

> make' :: (String :<: (INTM :=>: TY)) -> ProofState INTM
> make' (s :<: (ty :=>: tyv)) = do
>     aus <- getAuncles
>     s' <- pickName s
>     n <- withRoot (flip name s')
>     let  ty'  = liftType aus ty
>          ref  = n := HOLE :<: evTm ty'
>     root <- getDevRoot
>     putDevEntry (E ref (last n) (Girl LETG (B0, Unknown (ty :=>: tyv), room root s')) ty')
>     putDevRoot (roos root)
>     return (N (P ref $:$ aunclesToElims (aus <>> F0)))

> aunclesToElims :: Fwd (Entry Bwd) -> [Elim INTM]
> aunclesToElims F0 = []
> aunclesToElims (E ref _ (Boy _) _ :> es) = (A (N (P ref))) : aunclesToElims es
> aunclesToElims (_ :> es) = aunclesToElims es


> makeModule :: String -> ProofState ()
> makeModule s = do
>     n <- withRoot (flip name s)
>     root <- getDevRoot
>     putDevEntry (M n (B0, Module, room root s))
>     putDevRoot (roos root)

> pickName :: String -> ProofState String
> pickName ""  = do
>     r <- getDevRoot
>     return ("G" ++ show (snd r))
> pickName s   = return s


> moduleToGoal :: (INTM :=>: TY) -> ProofState INTM
> moduleToGoal (ty :=>: tyv) = do
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


The |piBoy| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piBoy :: (String :<: INTM) -> ProofState REF
> piBoy (s :<: ty) = piBoy' (s :<: (ty :=>: evTm ty))

> piBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> piBoy' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> do
>             root <- getDevRoot
>             Root.freshRef (s :<: tv)
>                 (\ref r ->  do
>                    putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>                    putDevRoot r
>                    return ref) root
>         Unknown _  -> throwError' "piBoy: goal is not of type SET."
>         _          -> throwError' "piBoy: only possible for incomplete goals."

The |select| command takes a term representing a neutral parameter, makes a new goal of the
same type, and fills it in with the parameter. \question{Is bquote really right here?}

> select :: INTM -> ProofState INTM
> select tm@(N (P (name := k :<: ty))) = do
>     root <- getDevRoot
>     make (fst (last name) :<: bquote B0 ty root)
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

> propagateNews :: NewsBulletin -> NewsyEntries -> ProofState NewsBulletin

If we have nothing to say and nobody to tell, we might as well give up and go home.

> propagateNews [] (NF F0) = return []

If there are no entries to process, we should tell the mother (if there is one),
stash the bulletin after the current location and stop. Note that the insertion is
optional because it will fail when we have reached the end of the module, at which
point everyone knows the news anyway.

> propagateNews news (NF F0) = do
>     news' <- tellMother news
>     optional (insertCadet news')
>     return news'

A |Boy| is relatively easy to deal with, we just check to see if its type
has become more defined, and pass on the good news if necessary.

> propagateNews news (NF (Right e@(E (name := DECL :<: tv) sn (Boy k) ty) :> es)) = do
>     case tellNews news ty of
>         (_, NoNews) -> putDevEntry (E (name := DECL :<: tv) sn (Boy k) ty) >> propagateNews news (NF es)
>         (ty', GoodNews) -> do
>             let ref = name := DECL :<: evTm ty'
>             putDevEntry (E ref sn (Boy LAMB) ty')
>             propagateNews ((ref, GoodNews):news) (NF es)

Updating girls is a bit more complicated. We proceed as follows:
\begin{enumerate}
\item Recursively propagate the news to the children. \question{does this create spurious |R|s?}
\item Call |tellGirl| to update the tip and definition (including their types)
\item Add the updated girl to the current development.
\item Continue propagating the latest news.
\end{enumerate}

> propagateNews news (NF ((Right e@(E ref sn (Girl LETG (_, tip, root)) ty)) :> es)) = do
>     (news', cs) <- propagateIn
>     (news'', e') <- tellGirl news' (E ref sn (Girl LETG (cs, tip, root)) ty)
>     putDevEntry e'
>     propagateNews news'' (NF es)
>   where
>     propagateIn :: ProofState (NewsBulletin, Entries)
>     propagateIn = do
>         xs <- jumpIn e
>         news' <- propagateNews news xs
>         goOut
>         Just (E _ _ (Girl LETG (cs, _, _)) _) <- removeDevEntry
>         return (news', cs)


> propagateNews news (NF (Right e@(M n d) :> es)) = do
>     xs <- jumpIn e
>     news' <- propagateNews news xs
>     goOut
>     propagateNews news (NF es)


Finally, if we encounter an older news bulletin when propagating news, we can simply
merge the two together.

> propagateNews news (NF (Left oldNews :> es)) = propagateNews (mergeNews news oldNews) (NF es)


> tellEntry :: NewsBulletin -> Entry Bwd -> ProofState (NewsBulletin, Entry Bwd)
> tellEntry news (M n d) = return (news, M n d)
> tellEntry news e = tellGirl news e

The |tellGirl| function informs a girl about a news bulletin that her children
should have already received. It will
\begin{enumerate}
\item update the tip type (and term, if there is one);
\item update the overall type of the entry;
\item re-evaluate the definition, if there is one; and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellGirl :: NewsBulletin -> Entry Bwd -> ProofState (NewsBulletin, Entry Bwd)
> tellGirl news (E (name := k :<: tv) sn (Girl LETG (cs, tip, root)) ty) = do
>     let  (tip', n)       = tellTip news tip
>          (ty', tv', n')  = tellNewsEval news ty tv
>     k' <- case k of
>             HOLE    -> return HOLE
>             DEFN _  -> do
>                 aus <- getGreatAuncles
>                 let Defined tm _ = tip'
>                 return (DEFN (evTm (parBind aus cs tm)))
>     let ref = name := k' :<: tv'
>     return (addNews news (ref, min n n'), E ref sn (Girl LETG (cs, tip', root)) ty')
>  where 
>    tellTip :: NewsBulletin -> Tip -> (Tip, News)
>    tellTip news (Unknown tt) =
>        let (tt', n) = tellTipType news tt in
>            (Unknown tt', n)
>    tellTip news (Defined tm tt) =
>        let (tt', n) = tellTipType news tt in
>            case tellNews news tm of
>                (_,    NoNews)    -> (Defined tm   tt', n)
>                (tm',  GoodNews)  -> (Defined tm'  tt', GoodNews)
>
>    tellTipType :: NewsBulletin -> (INTM :=>: TY) -> (INTM :=>: TY, News)
>    tellTipType news (tm :=>: ty) =
>        let (tm', ty', n) = tellNewsEval news tm ty in
>            (tm' :=>: ty',  n)


> tellMother :: NewsBulletin -> ProofState NewsBulletin
> tellMother news = (do
>     e <- getMotherEntry
>     (news', e') <- tellEntry news e 
>     putMotherEntry e'
>     return news'
>  ) <|> return news


The |tellNews| function applies a bulletin to a term. It returns the updated
term and the news about it.

> tellNews :: NewsBulletin -> Tm {d, TT} REF -> (Tm {d, TT} REF, News)
> tellNews []    tm = (tm, NoNews)
> tellNews news  tm = case foldMap (lookupNews news) tm of
>     NoNews  -> (tm, NoNews)
>     n       -> (fmap (getLatest news) tm, n)

The |tellNewsEval| function takes a bulletin, term and its present value. It updates
the term with the bulletin and re-evaluates it if necessary.

> tellNewsEval :: NewsBulletin -> INTM -> VAL -> (INTM, VAL, News)
> tellNewsEval news tm tv = case tellNews news tm of
>     (_,    NoNews)    -> (tm,   tv,        NoNews)
>     (tm',  GoodNews)  -> (tm',  evTm tm',  GoodNews)