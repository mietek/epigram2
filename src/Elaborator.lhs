\section{Proof State}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

> module Elaborator where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.Foldable
> import Data.Traversable

> import BwdFwd
> import Developments
> import PrettyPrint
> import Root
> import Rooty
> import Tm

%endif

\subsection{Proof Context}

Recall from Section~\ref{sec:developments} that

< type Dev = (Bwd Entry, Tip, Root)

We ``unzip`` (cf. Huet's Zipper) this type to produce a type representing its
one-hole context, which allows us to keep track of the location of a working
development and perform local navigation easily.
Each |Layer| of the structure is a record with the following fields:
\begin{description}
\item[|elders|] entries appearing above the working development
\item[|mother|] the |REF| of the |Entry| that contains the working development
\item[|cadets|] entries appearing below the working development
\item[|laytip|] the |Tip| of the containing development
\item[|layroot|] the |Root| of the containing development
\end{description}

> data Layer = Layer
>   {  elders  :: Bwd Entry
>   ,  mother  :: REF
>   ,  cadets  :: Fwd Entry
>   ,  laytip  :: Tip
>   ,  layroot :: Root }
>   deriving Show

The current proof context is then represented by a stack of |Layer|s, along with the
current working development:

> type ProofContext = (Bwd Layer, Dev)

The |auncles| function calculates the elder aunts or uncles of the current development,
thereby giving a list of entries that are currently in scope.

> auncles :: ProofContext -> Bwd Entry
> auncles (ls, (es, _, _)) = foldMap elders ls <+> es


\subsection{Proof State Monad}

The proof state monad provides access to the |ProofContext| as in a |State| monad,
but with the possibility of command failure represented by |Maybe|. 

> type ProofState = StateT ProofContext Maybe

Handily, |Maybe| is a |MonadPlus|, and |StateT| preserves this, so we can easily
make |ProofState| an |Alternative|:

> instance Applicative ProofState where
>     pure = return
>     (<*>) = ap

> instance Alternative ProofState where
>     empty = mzero
>     (<|>) = mplus

We provide various functions to get information from the proof state and store
updated information, providing a friendlier interface than |get| and |put|.

> getDev :: ProofState Dev
> getDev = gets snd

> getDevRoot :: ProofState Root
> getDevRoot = do
>     (_, _, root) <- getDev
>     return root

> getDevTip :: ProofState Tip
> getDevTip = do
>     (_, tip, _) <- getDev
>     return tip

> getLayer :: ProofState Layer
> getLayer = do
>     ls :< l <- gets fst
>     return l

> putDev :: Dev -> ProofState ()
> putDev dev = do
>     ls <- gets fst
>     put (ls, dev)

> putDevEntry :: Entry -> ProofState ()
> putDevEntry e = do
>     (es, tip, root) <- getDev
>     putDev (es :< e, tip, root)

> putDevRoot :: Root -> ProofState ()
> putDevRoot r = do
>     (es, tip, _) <- getDev
>     putDev (es, tip, r)

> putLayer :: Layer -> ProofState ()
> putLayer l = do
>     (ls, dev) <- get
>     put (ls :< l, dev)

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

> replaceLayer :: Layer -> ProofState Layer
> replaceLayer l = do
>     (ls :< l', dev) <- get
>     put (ls :< l, dev)
>     return l'


A |ProofState| is not |Rooty| because the semantics of the latter are not compatible
with the caching of |Root|s in the proof context. However, it can provide the current
|Root| to a function that requires it. Note that this function has no way to return
an updated root to the proof context, so it must not leave any references around
when it has finished.

> withRoot :: (Root -> x) -> ProofState x
> withRoot f = getDevRoot >>= return . f

Presumably we should be able to do something similar for running tactics?

< withTac :: TY -> Tac x -> ProofState x


\subsubsection{Proof State Navigation Commands}

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
> goIn = goInAcc F0 
>   where
>     goInAcc :: Fwd Entry -> ProofState ()
>     goInAcc cadets = do
>         (ls, (es :< e, tip, root)) <- get
>         case e of
>             E ref _ (Girl LETG dev) -> put (ls :< Layer es ref cadets tip root, dev)
>             _ -> put (ls, (es, tip, root)) >> goInAcc (e :> cadets)

> goOut :: ProofState ()
> goOut = do
>     Layer elders mother cadets tip root <- removeLayer
>     dev <- getDev
>     putDev (elders :< E mother (lastName mother) (Girl LETG dev) <>< cadets, tip, root)        

> goUp :: ProofState ()
> goUp = goUpAcc F0
>   where
>     goUpAcc :: Fwd Entry -> ProofState ()
>     goUpAcc acc = do
>         l@(Layer (es :< e) oldRef cadets tip root) <- removeLayer
>         oldDev <- getDev
>         case e of
>             E newRef _ (Girl LETG newDev) ->
>                 putDev newDev >>
>                 putLayer l{elders=es, mother=newRef,cadets=(acc <+> 
>                     (E oldRef (lastName oldRef) (Girl LETG oldDev) :> cadets))}
>             _ -> putLayer l{elders=es} >> goUpAcc (e :> acc)

> goDown :: ProofState ()
> goDown = goDownAcc B0
>   where
>     goDownAcc :: Bwd Entry -> ProofState ()
>     goDownAcc acc = do
>         l@(Layer elders ref (e :> es) tip root) <- removeLayer
>         case e of
>             E newRef _ (Girl LETG newDev) -> do
>                 oldDev <- replaceDev newDev
>                 putLayer  l{elders=(elders:<E ref (lastName ref) (Girl LETG oldDev)) <+> acc,
>                               mother=newRef, cadets=es}
>             _ -> putLayer l{cadets=es} >> goDownAcc (acc :< e)


The slightly dubious |appendBinding| and |appendGoal| commands add entries to the
working development, without type-checking.

> appendBinding :: (String :<: TY) -> BoyKind -> ProofState ()
> appendBinding x k = getDevRoot >>=
>     Root.freshRef x (\ref r -> putDevEntry (E ref (lastName ref) (Boy k)) >> putDevRoot r)

> appendGoal :: (String :<: TY) -> ProofState ()
> appendGoal (s:<:ty) = do
>     root <- getDevRoot
>     n <- withRoot (flip name s)
>     putDevEntry (E (n := HOLE :<: ty) (last n) (Girl LETG (B0, Unknown ty, room root s)))
>     putDevRoot (roos root)


\subsubsection{Goal Search Commands}

To implement goal search, we need a few useful bits of kit...

The |untilA| operator runs its first argument one or more times until its second
argument succeeds, at which point it returns the result. If the first argument
fails, the whole operation fails.

> untilA :: Alternative f => f () -> f a -> f a
> g `untilA` test = g *> try
>     where try = test <|> (g *> try)

The |much| operator runs its argument until it fails, then returns the state of
its last success.

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

> prevGoal :: ProofState ()
> prevGoal = ((goUp >> much goIn) <|> goOut) `untilA` isGoal

> nextGoal :: ProofState ()
> nextGoal = ((goIn >> much goUp) <|> goDown <|> (goOut `untilA` goDown)) `untilA` isGoal

\subsection{Command-Line Interface}

Here we have a very basic command-driven interface to the proof state monad.

> cochon :: ProofContext -> IO ()
> cochon loc@(ls, dev) = do
>     printDev dev
>     putStr (showPrompt ls)
>     l <- getLine
>     let ws = words l
>     if (head ws == "quit")
>         then return ()
>         else case runStateT (elabParse ws) loc of
>             Just (s, loc') -> do
>                 putStrLn s 
>                 printChanges (auncles loc) (auncles loc')
>                 cochon loc'
>             Nothing ->  putStrLn "I'm sorry, Dave. I'm afraid I can't do that."
>                         >> cochon loc

> elabParse :: [String] -> ProofState String
> elabParse ("in":_)       = goIn         >> return "Going in..."
> elabParse ("out":_)      = goOut        >> return "Going out..."
> elabParse ("up":_)       = goUp         >> return "Going up..."
> elabParse ("down":_)     = goDown       >> return "Going down..."
> elabParse ("top":_)      = much goUp    >> return "Going to top..."
> elabParse ("bottom":_)   = much goDown  >> return "Going to bottom..."
> elabParse ("module":_)     = much goOut   >> return "Going to module..."
> elabParse ("prev":_)     = prevGoal     >> return "Searching for previous goal..."
> elabParse ("next":_)     = nextGoal     >> return "Searching for next goal..."
> elabParse ("bind":s:_)   = appendBinding (s :<: C Set) LAMB >> return "Appended binding!"
> elabParse ("goal":s:_)   = appendGoal (s :<: C Set) >> return "Appended goal!"
> elabParse ("auncles":_)  = get >>= return . showEntries . (<>> F0) . auncles
> elabParse _ = return "???"

> showPrompt :: Bwd Layer -> String
> showPrompt (_ :< Layer _ (n := _) _ _ _)  = prettyName n ++ " > "
> showPrompt B0        = "> "

> printChanges :: Bwd Entry -> Bwd Entry -> IO ()
> printChanges as bs | as /= bs = do
>     let (lost, gained)  = diff (as <>> F0) (bs <>> F0)
>     if lost /= F0
>         then putStrLn ("Left scope: " ++ showEntries lost)
>         else putStrLn "Nothing went out of scope."
>     if gained /= F0
>        then putStrLn ("Entered scope: " ++ showEntries gained)
>        else putStrLn "Nothing came into scope."
> printChanges _ _ = return ()

> diff :: (Eq a) => Fwd a -> Fwd a -> (Fwd a, Fwd a)
> diff (x :> xs) (y :> ys)
>     | x == y     = diff xs ys
>     | otherwise  = (x :> xs, y :> ys)
> diff xs ys = (xs, ys)

> showEntries :: Fwd Entry -> String
> showEntries = foldMap (\(E ref _ _) -> show (prettyRef [] ref) ++ ", ")


\section{Elab Monad}

> data Elab x
>   = Bale x
>   | Cry
>   | Hope
>   | EDef String INTM (Elab INTM) (VAL -> Elab x)
>   | ELam String (VAL -> Elab x)
>   | EPi String INTM (VAL -> Elab x)

> instance Monad Elab where
>   return = Bale
>   Bale x        >>= k = k x
>   Cry           >>= k = Cry
>   Hope          >>= k = Hope
>   EDef x y d f  >>= k = EDef x y d ((k =<<) . f)
>   ELam x f      >>= k = ELam x ((k =<<) . f)
>   EPi x y f     >>= k = EPi x y ((k =<<) . f)
>
> instance Functor Elab where
>   fmap = ap . return
>
> instance Applicative Elab where
>   pure = return
>   (<*>) = ap
