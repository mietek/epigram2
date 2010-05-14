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
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import ProofState.Developments
> import ProofState.News
> import ProofState.Lifting
> import ProofState.ProofContext
> import ProofState.ProofState

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

We have to use a boot file to resolve the circular dependency between this module
and |Elaboration.Wire|. We need to make calls to the news propagation code from
navigation commands, but the news code uses proof state manipulation commands
defined here.

> import {-# SOURCE #-} Elaboration.Wire

> import Evidences.Tm
> import Evidences.Rules

%endif

\question{There are some serious re-ordering of functions to be done
here, in order to improve the narrative.}


\subsection{Asking for Evidence}

A |ProofState| is almost a |NameSupplier|, but it cannot fork the
name supply.

> instance NameSupplier (ProofStateT e) where
>     freshRef (s :<: ty) f = do
>         nsupply <- getDevNSupply
>         freshRef (s :<: ty) (\ref nsupply' -> do
>             putDevNSupply nsupply'
>             f ref
>           ) nsupply
>
>     forkNSupply = error "ProofState does not provide forkNSupply"
>     
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply
to proof state commands.

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


Similarly, |checkHere| type-checks a term using the local name supply...

> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere (ty :>: tm) = do
>     mc <- withNSupply $ liftError . (typeCheck $ check (ty :>: tm))
>     lift mc

... and |inferHere| infers the type of a term using the local name supply.

> inferHere :: EXTM -> ProofState (VAL :<: TY)
> inferHere tm = do
>     mc <- withNSupply $ liftError . (typeCheck $ infer tm)
>     lift mc



The |validateHere| performs some checks on the current location, which
may be useful for paranoia purposes.

> validateHere :: ProofState ()
> validateHere = do
>     m <- getMother
>     case m of
>         GirlMother (_ := DEFN tm :<: ty) _ _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: girl type failed to type-check: SET does not admit"
>                              ++ errTyVal (ty :<: SET))
>             tm' <- bquoteHere tm
>             checkHere (ty :>: tm')
>                 `pushError`  (err "validateHere: definition failed to type-check:"
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "does not admit"
>                              ++ errTyVal (tm :<: ty))
>             return ()
>         GirlMother (_ := HOLE _ :<: ty) _ _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: hole type failed to type-check: SET does not admit" 
>                              ++ errTyVal (ty :<: SET))
>             return ()
>         _ -> return ()


> withGoal :: (VAL -> ProofState ()) -> ProofState ()
> withGoal f = do
>   (_ :=>: goal) <- getGoal "withGoal"
>   f goal


\subsection{Navigation Commands}

\subsubsection{Single-step Navigation}

First, some vocabulary. The \emph{focus} is the current development; it contains
a \emph{cursor} which is the point at which changes take place. Consider
the following example:

\begin{verbatim}
[
  A := ? : S
  B [
    D := ? : S
    \ x : S
    E := ? : S
    \ y : S ___ cursor here
  ] : S
  C := ? : S
]
\end{verbatim}

Suppose the cursor is initially at the bottom of the development |B|, which
is in focus. We provide the following commands to navigate the proof state:
\begin{itemize}
\item |cursorUp| moves the cursor up by one entry (under |E| in the example);
\item |cursorDown| moves the cursor down by one entry (illegal in the example);
\item |goIn| moves the focus into the girl or module above the cursor,
      and leaves the cursor at the bottom of the development
      (inside |E| in the example);
\item |goOut| moves the focus out to the development that contains it, with
      the cursor at the bottom of the development (under |C| in the example);
\item |goOutProperly| moves the focus out to the development that contains
      it, with the cursor under the previously focused entry
      (under |B| in the example);
\item |goUp| moves the focus to the next eldest girl or module and leaves the
      cursor at the bottom (inside |A| in the example); and
\item |goDown| moves the focus to the next youngest girl or module and leaves
      the cursor at the bottom (inside |C| in the example).
\end{itemize}

These commands fail with an error if they are impossible because the
proof context is not in the required form. Things are slightly more complicated
than the above description because of the possibility of news bulletins below
the cursor; as these are propagated lazily, they must be pushed down when the
cursor or focus move.

The |cursorUp| and |cursorDown| commands are straightforward, because there
is no news to worry about. We simply move an entry above the cursor to one
below, or vice versa.

> cursorUp :: ProofState ()
> cursorUp = do
>     es' <- getDevEntries
>     case es' of
>         es :< e -> do
>             cadets <- getDevCadets
>             putDevEntries es
>             putDevCadets (e :> cadets)
>             return ()
>         B0 -> throwError' $ err "cursorUp: cannot move cursor up."

> cursorDown :: ProofState ()
> cursorDown = do
>     es <- getDevEntries
>     cadets' <- getDevCadets
>     case cadets' of
>         cadet :> cadets -> do
>             putDevEntries (es :< cadet)
>             putDevCadets cadets
>             return ()
>         F0 -> throwError' $ err "cursorDown: cannot move cursor down."

The |goIn| command has no news to worry about either; it simply moves the
cursor upwards until it finds an entry with a development, then enters it.

> goIn :: ProofState ()
> goIn = do
>     es' <- getDevEntries
>     case es' of
>         B0 -> throwError' $ err "goIn: you can't go that way."
>         es :< e -> case entryDev e of
>           Nothing   -> cursorUp >> goIn
>           Just dev  -> do
>              cadets <- getDevCadets
>              tip <- getDevTip
>              nsupply <- getDevNSupply
>              putLayer (Layer es (entryToMother e) (reverseEntries cadets)
>                            tip nsupply)
>              putDev dev
>              putDevCadets F0
>              return ()


The |goOut| command has to deal with any news that may be present in the cadets
of the current layer (i.e. down from the focus). It updates the cadets,
starting with the empty bulletin, so it ends up with the cursor at the bottom
of the new focus.

> goOut :: ProofState ()
> goOut = do
>     e <- getMotherEntry
>     ml <- optional removeLayer
>     case ml of
>         Just l -> do
>             putDev (elders l :< e, laytip l, laynsupply l)
>             putDevCadets F0
>             propagateNews True [] (cadets l)
>             return ()
>         Nothing -> throwError' $ err "goOut: you can't go that way."


The |goOutProperly| variant calls |goOut|, then moves the cursor back up to
just below the previous focus.

> goOutProperly :: ProofState ()
> goOutProperly = do
>     ls <- getLayers
>     case ls of
>         _ :< Layer{cadets=cadets} -> do
>             goOut
>             Data.Traversable.mapM (const cursorUp) cadets
>             return ()
>         B0 -> throwError' $ err "goOutProperly: you can't go that way."


The |goUp| command looks through the layer elders for one that has a
development, accumulating boys it passes over so they be put back as
layer cadets at the new focus.

> goUp :: ProofState ()
> goUp = goUpAcc (NF F0)
>   where
>     goUpAcc :: NewsyEntries -> ProofState ()
>     goUpAcc (NF acc) = do
>         l <- getLayer
>         case l of
>           (Layer (es :< e) m (NF cadets) tip nsupply) -> case entryDev e of
>             Just dev -> do
>                 me <- getMotherEntry
>                 putDev dev
>                 putDevCadets F0
>                 replaceLayer l{elders=es, mother=entryToMother e,
>                     cadets=NF (acc <+> (Right (reverseEntry me) :> cadets))}
>                 return ()
>             Nothing -> do
>                 replaceLayer l{elders=es}
>                 goUpAcc (NF (Right (reverseEntry e) :> acc))
>           _ -> throwError' $ err "goUp: you can't go that way."


The |goDown| command looks through the layer cadets for one that has a
development, passing on news it encounters as it goes and accumulating
boys so they can be put back as layer elders at the new focus.

> goDown :: ProofState ()
> goDown = goDownAcc B0 []
>   where
>     goDownAcc :: Entries -> NewsBulletin -> ProofState ()
>     goDownAcc acc news = do
>         l <- getLayer
>         case l of
>           (Layer elders _ (NF (ne :> es)) _ _) -> case ne of
>             Left nb -> do
>                 replaceLayer l{cadets=NF es}
>                 goDownAcc acc (mergeNews news nb)
>             Right e -> case entryCoerce e of
>               Left (es', tip', nsupply') ->  do
>                 me <- getMotherEntry
>                 replaceLayer l{elders=(elders :< me) <+> acc,
>                                    mother=entryToMother e, cadets=NF es}
>                 putDev (B0, tip', nsupply')
>                 putDevCadets F0
>                 news' <- propagateNews True news es'
>                 return ()
>               Right e' -> do
>                 (news', e'') <- tellEntry news e'
>                 replaceLayer l{cadets=NF es}
>                 goDownAcc (acc :< e'') news'
>           _ -> throwError' $ err "goDown: you can't go that way."


\subsubsection{Many-step Navigation}

The |cursorTop|, |cursorBottom|, |goTop|, |goBottom| and |goRoot| commands
apply the corresponding single-step commands zero or more times.

> cursorTop :: ProofState ()
> cursorTop = much cursorUp

> cursorBottom :: ProofState ()
> cursorBottom = much cursorDown

> goTop :: ProofState ()
> goTop = much goUp

> goBottom :: ProofState ()
> goBottom = much goDown

> goRoot :: ProofState ()
> goRoot = much goOut


The |goTo| command moves the focus to the entry with the given long name,
starting from the root module.

> goTo :: Name -> ProofState ()
> goTo name = goRoot >> goTo' name
>   where
>     goTo' :: Name -> ProofState ()
>     goTo' [] = return ()
>     goTo' (xn:xns) = (seek xn >> goTo' xns)
>         `pushError` (err "goTo: could not find " ++ err (showName (xn:xns)))
>
>     seek :: (String, Int) -> ProofState ()
>     seek xn = do
>         goIn
>         m <- getMotherName
>         if xn == last m
>             then return ()
>             else goUp `untilA` (guard . (== xn) . last =<< getMotherName)


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
> prevStep = ((goUp >> much goIn) <|> goOut) `pushError` (err "prevStep: no previous steps.")
>
> prevGoal :: ProofState ()
> prevGoal = (prevStep `untilA` isGoal) `pushError` (err "prevGoal: no previous goals.")
>
> nextStep :: ProofState ()
> nextStep = ((goIn >> goTop) <|> goDown <|> (goOut `untilA` goDown))
>                `pushError` (err "nextStep: no more steps.")
>
> nextGoal :: ProofState ()
> nextGoal = (nextStep `untilA` isGoal) `pushError` (err "nextGoal: no more goals.")


Sometimes we want to stay at the current location if it is a goal, and go
to the next goal otherwise.

> seekGoal :: ProofState ()
> seekGoal = isGoal <|> nextGoal


\subsection{Module Commands}


> makeModule :: String -> ProofState Name
> makeModule s = do
>     n <- withNSupply (flip mkName s)
>     nsupply <- getDevNSupply
>     putDevEntry (M n (B0, Module, freshNSpace nsupply s))
>     putDevNSupply (freshName nsupply)
>     return n

> moduleToGoal :: INTM -> ProofState (EXTM :=>: VAL)
> moduleToGoal ty = do
>     (_ :=>: tyv) <- checkHere (SET :>: ty)
>     ModuleMother n <- getMother
>     aus <- getAuncles
>     let  ty' = liftType aus ty
>          ref = n := HOLE Waiting :<: evTm ty'
>     putMother (GirlMother ref (last n) ty' Nothing)
>     putDevTip (Unknown (ty :=>: tyv))
>     return (applyAuncles ref aus)

> draftModule :: String -> ProofState t -> ProofState t
> draftModule name draftyStuff = do
>     makeModule name
>     goIn
>     t <- draftyStuff
>     goOutProperly
>     mm <- removeDevEntry
>     case mm of
>         Just (M _ _) -> return t
>         _ -> throwError' . err $ "draftModule: drafty " ++ name
>                                  ++ " did not end up in the right place!"


The |lookupName| function looks up a name in the context (including axioms and
primitives); if found, it returns the reference applied to the spine of
shared parameters.

> lookupName :: Name -> ProofStateT e (Maybe (EXTM :=>: VAL))
> lookupName name = do
>     aus <- getAuncles
>     case Data.Foldable.find ((name ==) . entryName) aus of
>       Just (E ref _ _ _)  -> return (Just (applyAuncles ref aus))
>       Nothing             ->
>         case Data.Foldable.find ((name ==) . refName . snd) (axioms ++ primitives) of
>           Just (_, ref)  -> return (Just (applyAuncles ref aus))
>           Nothing        -> return Nothing



\subsection{Construction Commands}

Various commands yield an |EXTM :=>: VAL|, and we sometimes need to convert
this to an |INTM :=>: VAL|:

> neutralise :: Monad m => (EXTM :=>: VAL) -> m (INTM :=>: VAL)
> neutralise (n :=>: v) = return (N n :=>: v)

The |apply| command checks if the last entry in the development is a girl $y$ with type
$\Pi S T$ and if so, adds a goal of type $S$ and applies $y$ to it.

> apply :: ProofState (EXTM :=>: VAL)
> apply = do
>   devEntry <- getDevEntry
>   case devEntry of
>     E ref@(name := k :<: (PI s t)) _ (Girl LETG _ _) _ -> do
>         s' <- bquoteHere s
>         t' <- bquoteHere (t $$ A s)
>         z :=>: _ <- make ("z" :<: s')
>         make ("w" :<: t')
>         goIn
>         give (N (P ref :$ A (N z)))
>     _ -> throwError' $ err  $ "apply: last entry in the development" 
>                             ++ " must be a girl with a pi-type."

The |done| command checks if the last entry in the development is a girl, and if so,
fills in the goal with this entry.

> done :: ProofState (EXTM :=>: VAL)
> done = do
>   devEntry <- getDevEntry
>   case devEntry of
>     E ref _ (Girl LETG _ _) _ -> give (N (P ref))
>     _ -> throwError' $ err "done: last entry in the development must be a girl."

The |give| command checks the provided term has the goal type, and if so, fills in
the goal, updates the reference and goes out. The |giveNext| variant moves to the
next goal (if one exists) instead.

> give :: INTM -> ProofState (EXTM :=>: VAL)
> give tm = give' tm <* goOutProperly

> giveNext :: INTM -> ProofState (EXTM :=>: VAL)
> giveNext tm = give' tm <* (nextGoal <|> goOut)

> give' :: INTM -> ProofState (EXTM :=>: VAL)
> give' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             mc <- withNSupply $ liftError . (typeCheck $ check (tipTy :>: tm))
>             mc `catchEither`  (err "give: typechecking failed:"
>                               ++ errInTm tm
>                               ++ err "is not of type"
>                               ++ errTyVal (tipTy :<: SET))
>             aus <- getGreatAuncles
>             sibs <- getDevEntries
>             let tmv = evTm (parBind aus sibs tm)
>             GirlMother (name := _ :<: tyv) xn ty ms <- getMother
>             let ref = name := DEFN tmv :<: tyv
>             putDevTip (Defined tm (tipTyTm :=>: tipTy))
>             putMother (GirlMother ref xn ty ms)
>             updateRef ref
>             return (applyAuncles ref aus)
>         _  -> throwError' $ err "give: only possible for incomplete goals."

The |lambdaBoy| command checks that the current goal is a $\Pi$-type, and if so,
appends a $\lambda$-abstraction with the appropriate type to the current development.

> lambdaBoy :: String -> ProofState REF
> lambdaBoy x = do
>     tip <- getDevTip
>     case tip of
>       Unknown (pi :=>: ty) -> case lambdable ty of
>         Just (k, s, t) -> freshRef (x :<: s) (\ref -> do
>             s' <- bquoteHere s
>             putDevEntry (E ref (lastName ref) (Boy k) s')
>             let tipTyv = t (pval ref)
>             tipTy <- bquoteHere tipTyv
>             putDevTip (Unknown (tipTy :=>: tipTyv))
>             return ref
>           )
>         _  -> throwError' $ err "lambdaBoy: goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaBoy: only possible for incomplete goals."

The |lambdaBoy'| variant allows a type to be specified, so it can
be used with modules. If used at an |Unknown| tip, it will check
that the supplied type matches the one at the tip.

> lambdaBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> lambdaBoy' (x :<: (ty :=>: tv))  = do
>     tip <- getDevTip
>     case tip of
>       Module -> freshRef (x :<: tv) (\ref -> do
>           putDevEntry (E ref (lastName ref) (Boy LAMB) ty)
>           return ref
>         )
>       Unknown (pi :=>: gty) -> case lambdable gty of
>         Just (k, s, t) -> do
>           eq <- withNSupply (equal (SET :>: (tv, s)))
>           if eq
>             then freshRef (x :<: tv) (\ref -> do
>                 putDevEntry (E ref (lastName ref) (Boy k) ty)
>                 let tipTyv = t (pval ref)
>                 tipTy <- bquoteHere tipTyv
>                 putDevTip (Unknown (tipTy :=>: tipTyv))
>                 return ref
>               )
>             else throwError' $ err "lambdaBoy': given type does not match domain of goal."
>         _  -> throwError' $ err "lambdaBoy': goal is not a pi-type or all-proof."
>       _    -> throwError' $ err "lambdaBoy': only possible for modules or incomplete goals."


The following piece of kit might profitably be shifted to somewhere more
general.

> lambdable :: TY -> Maybe (BoyKind, TY, VAL -> TY)
> lambdable (PI s t)         = Just (LAMB, s, (t $$) . A)
> lambdable (PRF (ALL s p))  = Just (ALAB, s, \v -> PRF (p $$ A v))
> lambdable _                = Nothing


The |make| command adds a named goal of the given type to the bottom of the
current development, after checking that the purported type is in fact a type.

> make :: (String :<: INTM) -> ProofState (EXTM :=>: VAL)
> make = make' Waiting

> make' :: HKind -> (String :<: INTM) -> ProofState (EXTM :=>: VAL)
> make' hk (s :<: ty) = do
>     _ :=>: tyv <- checkHere (SET :>: ty) `pushError`  (err "make: " 
>                              ++ errInTm ty 
>                              ++ err " is not a set.")
>     aus <- getAuncles
>     s' <- pickName "G" s
>     n <- withNSupply (flip mkName s')
>     let  ty'  = liftType aus ty
>          ref  = n := HOLE hk :<: evTm ty'
>     nsupply <- getDevNSupply
>     putDevEntry (E ref (last n) (Girl LETG (B0, Unknown (ty :=>: tyv), freshNSpace nsupply s') Nothing) ty')
>     putDevNSupply (freshName nsupply)
>     return (applyAuncles ref aus)


The |pickName| command takes a prefix suggestion and a name suggestion
(either of which may be empty), and returns a more-likely-to-be-unique
name if the name suggestion is empty.

> pickName :: String -> String -> ProofState String
> pickName "" s = pickName "x" s
> pickName prefix ""  = do
>     m <- getMotherName
>     r <- getDevNSupply
>     return (prefix ++ show (foldMap snd m + snd r))
> pickName _ s   = return s


The |piBoy| command checks that the current goal is of type SET, and that the supplied type
is also a set; if so, it appends a $\Pi$-abstraction to the current development.

> piBoy :: (String :<: INTM) -> ProofState REF
> piBoy (s :<: ty) = checkHere (SET :>: ty) >>= piBoy' . (s :<:)

> piBoy' :: (String :<: (INTM :=>: TY)) -> ProofState REF
> piBoy' (s :<: (ty :=>: tv)) = do
>     tip <- getDevTip
>     case tip of
>         Unknown (_ :=>: SET) -> freshRef (s :<: tv) (\ref -> do
>             putDevEntry (E ref (lastName ref) (Boy PIB) ty)
>             return ref
>           )
>         Unknown _  -> throwError' $ err "piBoy: goal is not of type SET."
>         _          -> throwError' $ err "piBoy: only possible for incomplete goals."

The |select| command takes a term representing a neutral parameter, makes a new
goal of the same type, and fills it in with the parameter.

> select :: INTM -> ProofState (EXTM :=>: VAL)
> select tm@(N (P (name := k :<: ty))) = do
>     ty' <- bquoteHere ty
>     make (fst (last name) :<: ty')
>     goIn
>     give tm
> select _ = throwError' $ err "select: term is not a parameter."
     
The |ungawa| command looks for a truly obvious thing to do, and does it.

> ignore :: ProofState a -> ProofState ()
> ignore f = do
>     f
>     return ()

> ungawa :: ProofState ()
> ungawa = (ignore done <|> ignore apply <|> ignore (lambdaBoy "ug"))
>     `pushError` (err "ungawa: no can do.")



\subsection{Information Commands}

> infoAuncles :: ProofState String
> infoAuncles = do
>     pc <- get
>     aus <- getAuncles
>     return (showEntries (inBScope pc) aus)

> infoDump :: ProofState String
> infoDump = gets show


The |getFakeMother| command returns a neutral application of a fake reference
that represents the mother of the current location. Note that its type is
$\lambda$-lifted over its great uncles, but it is then applied to them (as
shared parameters).

> getFakeMother :: Bool -> ProofState (EXTM :=>: VAL)
> getFakeMother includeLast = do
>    GirlMother (mnom := HOLE _ :<: ty) _ _ _ <- getMother
>    aus <- getAuncles
>    let xs = if includeLast
>                 then boySpine aus
>                 else init (boySpine aus)
>        tm = P (mnom := FAKE :<: ty) $:$ xs
>    return $ tm :=>: evTm tm