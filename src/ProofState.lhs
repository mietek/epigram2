%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

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

< type Dev = (Bwd Entry, Tip, Root)

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
>   {  elders  :: Bwd Entry
>   ,  mother  :: REF
>   ,  motherTy :: INTM
>   ,  cadets  :: Fwd Entry
>   ,  laytip  :: Tip
>   ,  layroot :: Root }
>   deriving Show

The current proof context is then represented by a stack of |Layer|s, along with the
current working development.

> type ProofContext = (Bwd Layer, Dev)

> emptyContext :: ProofContext
> emptyContext = (B0, (B0, Module, (B0, 0)))


The |greatAuncles| function returns the elder aunts or uncles of the current development,
not including its contents.

> greatAuncles :: ProofContext -> Bwd Entry
> greatAuncles (ls, _) = foldMap elders ls

The |auncles| function returns the elder aunts or uncles of the current insertion point,
including the contents of the current development, thereby giving a list of entries that
are currently in scope.

> auncles :: ProofContext -> Bwd Entry
> auncles c@(_, (es, _, _)) = greatAuncles c <+> es


\section{Proof State Monad}
\label{sec:proofStateMonad}

The proof state monad provides access to the |ProofContext| as in a |State| monad,
but with the possibility of command failure represented by |Maybe|. 

> type ProofState = StateT ProofContext (Either [String])

Handily, |Maybe| is a |MonadPlus|, and |StateT| preserves this, so we can easily
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

> getAuncles :: ProofState (Bwd Entry)
> getAuncles = get >>= return . auncles

> getDev :: ProofState Dev
> getDev = gets snd

> getDevEntries :: ProofState (Bwd Entry)
> getDevEntries = do
>     (es, _, _) <- getDev
>     return es

> getDevEntry :: ProofState Entry
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

> getGreatAuncles :: ProofState (Bwd Entry)
> getGreatAuncles = get >>= return . greatAuncles

> getLayer :: ProofState Layer
> getLayer = do
>     ls :< l <- getLayers
>     return l

> getLayers :: ProofState (Bwd Layer)
> getLayers = gets fst

> getMother :: ProofState REF
> getMother = do
>     l <- getLayer
>     return (mother l)

> getMotherEntry :: ProofState Entry
> getMotherEntry = do
>     l <- getLayer
>     dev <- getDev
>     return (E (mother l) (lastName (mother l)) (Girl LETG dev) (motherTy l))

> getMotherName :: ProofState Name
> getMotherName = do
>     ls <- gets fst
>     case ls of
>         (_ :< Layer{mother=name := _}) -> return name
>         B0 -> return []

> insertCadet :: Entry -> ProofState ()
> insertCadet e = do
>     l <- getLayer
>     replaceLayer l{cadets = e :> cadets l}
>     return ()

> putDev :: Dev -> ProofState ()
> putDev dev = do
>     ls <- gets fst
>     put (ls, dev)

> putDevEntry :: Entry -> ProofState ()
> putDevEntry e = do
>     (es, tip, root) <- getDev
>     putDev (es :< e, tip, root)

> putDevEntries :: Bwd Entry -> ProofState ()
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

> putMother :: REF -> ProofState ()
> putMother ref = do
>     l <- getLayer
>     _ <- replaceLayer l{mother=ref}
>     return ()

> putMotherEntry :: Entry -> ProofState ()
> putMotherEntry (E ref _ (Girl LETG dev) ty) = do
>     l <- getLayer
>     replaceLayer (l{mother=ref, motherTy=ty})
>     putDev dev

> removeDevEntry :: ProofState (Maybe Entry)
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

> replaceDev :: Dev -> ProofState Dev
> replaceDev dev = do
>     (ls, dev') <- get
>     put (ls, dev)
>     return dev'

> replaceDevEntries :: Bwd Entry -> ProofState (Bwd Entry)
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
> goIn = goInAcc F0 `replaceError` "goIn: you can't go that way."
>   where
>     goInAcc :: Fwd Entry -> ProofState ()
>     goInAcc cadets = do
>         (ls, (es :< e, tip, root)) <- get
>         case e of
>             E ref _ (Girl LETG dev) ty -> put (ls :< Layer es ref ty cadets tip root, dev)
>             _ -> put (ls, (es, tip, root)) >> goInAcc (e :> cadets)

> goOut :: ProofState ()
> goOut = (do
>     e <- getMotherEntry
>     l <- removeLayer
>     putDev (elders l :< e, laytip l, layroot l)
>     propagateNews [] (cadets l)
>     return ()
>   ) `replaceError` "goOut: you can't go that way."

> goOutSilently :: ProofState ()
> goOutSilently = do
>     e <- getMotherEntry
>     l <- removeLayer
>     putDev (elders l :< e <>< cadets l, laytip l, layroot l)

> goUp :: ProofState ()
> goUp = goUpAcc F0 `replaceError` "goUp: you can't go that way."
>   where
>     goUpAcc :: Fwd Entry -> ProofState ()
>     goUpAcc acc = do
>         l@(Layer (es :< e) oldRef oldTy cadets tip root) <- removeLayer
>         oldDev <- getDev
>         case e of
>             E newRef _ (Girl LETG newDev) newTy ->
>                 putDev newDev >>
>                 putLayer l{elders=es, mother=newRef, motherTy=newTy, cadets=(acc <+> 
>                     (E oldRef (lastName oldRef) (Girl LETG oldDev) oldTy :> cadets))}
>             _ -> putLayer l{elders=es} >> goUpAcc (e :> acc)

> goDown :: ProofState ()
> goDown = goDownAcc B0 [] `replaceError` "goDown: you can't go that way."
>   where
>     goDownAcc :: Bwd Entry -> NewsBulletin -> ProofState ()
>     goDownAcc acc news = do
>         l@(Layer elders ref ty (e :> es) tip root) <- removeLayer
>         case e of
>             E _ _ (Girl LETG newDev) _ -> do
>                 oldDev <- replaceDev newDev
>                 news' <- propagateNewsHere news
>                 (news'', E newRef _ (Girl LETG newDev') newTy) <- tellGirl news' e
>                 replaceDev newDev'
>                 putLayer  l{elders=(elders:<E ref (lastName ref) (Girl LETG oldDev) ty)<+> acc,
>                               mother=newRef, motherTy=newTy, cadets=R news'' :> es}
>             R nb  -> putLayer l{cadets=es} >> goDownAcc acc (mergeNews nb news)
>             _     -> putLayer l{cadets=es} >> goDownAcc (acc :< e) news

> goTo :: Name -> ProofState ()
> goTo [] = return ()
> goTo (xn:xns) = (seek xn >> goTo xns)
>     `replaceError` ("goTo: could not find " ++ showName (xn:xns))
>   where
>     seek :: (String, Int) -> ProofState ()
>     seek xn = (goUp <|> goIn) >> do
>         m := _ <- getMother
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
>     give (bquote B0 (pval ref $$ A s) root)
>     return ()
>   ) `replacePMF` "apply: last entry in the development must be a girl with a pi-type."

The |done| command checks if the last entry in the development is a girl, and if so,
fills in the goal with this entry.

> done :: ProofState()
> done = (do
>     E ref _ (Girl LETG _) _ <- getDevEntry
>     give (N (P ref))
>  ) `replacePMF` "done: last entry in the development must be a girl."

The |give| command checks the provided term has the goal type, and if so, fills in
the goal and updates the reference.

> give :: INTM -> ProofState ()
> give tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             aus <- getGreatAuncles
>             sibs <- getDevEntries
>             let tmv = evTm (parBind aus sibs tm)
>             name := _ :<: ty <- getMother
>             let ref = name := DEFN tmv :<: ty
>             putMother ref
>             updateRef ref
>             goOut
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
>             name := _ :<: ty <- getMother
>             let ref = name := DEFN tmv :<: ty
>             putMother ref
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
>     putDevEntry (E ref (last n) (Girl LETG (B0, Unknown (ty' :=>: tyv), room root s')) ty')
>     putDevRoot (roos root)
>     return (N (P ref))


> pickName :: String -> ProofState String
> pickName ""  = do
>     r <- getDevRoot
>     return ("G" ++ show (snd r))
> pickName s   = return s


The |piBoy| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piBoy :: (String :<: INTM) -> ProofState ()
> piBoy (s :<: ty) = piBoy' (s :<: (ty :=>: evTm ty))

> piBoy' :: (String :<: (INTM :=>: TY)) -> ProofState ()
> piBoy' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> do
>             root <- getDevRoot
>             Root.freshRef (s :<: tv)
>                 (\ref r ->  putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>                             >> putDevRoot r) root
>         Unknown _  -> throwError' "piBoy: goal is not of type SET."
>         _          -> throwError' "piBoy: only possible for incomplete goals."

The |select| command takes a term representing a neutral parameter, makes a new goal of the
same type, and fills it in with the parameter. \question{Is bquote really right here?}

> select :: INTM -> ProofState ()
> select tm@(N (P (name := k :<: ty))) = do
>     root <- getDevRoot
>     make (fst (last name) :<: bquote B0 ty root)
>     goIn
>     give tm
> select _ = throwError' "select: term is not a parameter."
     
The |ungawa| command looks for a truly obvious thing to do, and does it.

> ungawa :: ProofState ()
> ungawa = (done <|> apply <|> (lambdaBoy "ug" >> return ())) `replaceError` "ungawa: no can do."



\section{Wire Service}

Here we describe how to handle updates to references in the proof state, caused by
refinement commands like |give|. The idea is to deal with updates lazily, to avoid
unnecessary traversals of the proof tree. When |updateRef| is called to announce
a changed reference (that the current development has already processed), it simply
inserts a news bulletin below the current development.

> updateRef :: REF -> ProofState ()
> updateRef ref = insertCadet (R [(ref, GoodNews)])


The |propagateNews| function takes a current news bulletin and a list of entries
to add to the current development. It applies the news bulletin to each entry
in turn, picking up other bulletins along the way. This function should be called
when navigating to a development that may contain news bulletins, so they can be
pushed out of sight.

> propagateNews :: NewsBulletin -> Fwd Entry -> ProofState NewsBulletin

If we have nothing to say and nobody to tell, we might as well give up and go home.

> propagateNews [] F0 = return []

If there are no entries to process, we should tell the mother (if there is one),
stash the bulletin after the current location and stop. Note that the insertion is
optional because it will fail when we have reached the end of the module, at which
point everyone knows the news anyway.

> propagateNews news F0 = do
>     news' <- tellMother news
>     optional (insertCadet (R news'))
>     return news'

A |Boy| is relatively easy to deal with, we just check to see if its type
has become more defined, and pass on the good news if necessary.

> propagateNews news (e@(E (name := DECL :<: tv) sn (Boy _) ty) :> es) = do
>     case tellNews news ty of
>         (_, NoNews) -> putDevEntry e >> propagateNews news es
>         (ty', GoodNews) -> do
>             let ref = name := DECL :<: evTm ty'
>             putDevEntry (E ref sn (Boy LAMB) ty')
>             propagateNews ((ref, GoodNews):news) es

Updating girls is a bit more complicated. We proceed as follows:
\begin{enumerate}
\item Recursively propagate the news to the children. \question{does this create spurious |R|s?}
\item Call |tellGirl| to update the tip and definition (including their types)
\item Add the updated girl to the current development.
\item Continue propagating the latest news.
\end{enumerate}

> propagateNews news (e@(E ref sn (Girl LETG (_, tip, root)) ty) :> es) = do
>     (news', cs) <- propagateIn news e
>     (news'', e') <- tellGirl news' (E ref sn (Girl LETG (cs, tip, root)) ty)
>     putDevEntry e'
>     propagateNews news'' es
>  where
>    propagateIn :: NewsBulletin -> Entry -> ProofState (NewsBulletin, Bwd Entry)
>    propagateIn news e = do
>        putDevEntry e
>        goIn
>        news' <- propagateNewsHere news
>        goOut
>        Just (E _ _ (Girl LETG (cs, _, _)) _) <- removeDevEntry
>        return (news', cs)

Finally, if we encounter an older news bulletin when propagating news, we can simply
merge the two together.

> propagateNews news (R oldNews :> es) = propagateNews (mergeNews oldNews news) es


The |tellGirl| function informs a girl about a news bulletin that her children
should have already received. It will
\begin{enumerate}
\item update the tip type (and term, if there is one);
\item update the overall type of the entry;
\item re-evaluate the definition, if there is one; and
\item update the news bulletin with news about this girl.
\end{enumerate}

> tellGirl :: NewsBulletin -> Entry -> ProofState (NewsBulletin, Entry)
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
>     (news', e') <- tellGirl news e 
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


The |propagateNewsHere| function is a special case of |propagateNews| that
simply processes the current development.

> propagateNewsHere :: NewsBulletin -> ProofState NewsBulletin
> propagateNewsHere news = do
>     es <- replaceDevEntries B0
>     propagateNews news (es <>> F0)