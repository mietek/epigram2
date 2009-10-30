
%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Elaborator where

> import Data.Foldable
> import Control.Monad
> import Control.Applicative
> import Data.Traversable

> import BwdFwd
> import Developments
> import Root
> import Tm

%endif

\section{Dev Zipper}

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

The current proof state is then represented by a stack of |Layer|s, along with the
current working development:

> type ProofState = (Bwd Layer, Dev)

Now we need functions to manipulate the unzipped data structure.

|goIn| changes the current location to the bottom-most girl in the current development.

> goIn :: ProofState -> ProofState
> goIn l = goInAcc l F0 
>     where goInAcc :: ProofState -> Fwd Entry -> ProofState
>           goInAcc (ls, (es :< e, tip, root)) cadets =
>               case e of
>                   E ref _ (Girl LETG dev) ->
>                       (ls :< Layer es ref cadets tip root, dev)
>                   e -> goInAcc (ls, (es, tip, root)) (e :> cadets)
>           goInAcc _ _ = error "goIn: no girls in current development"


|goOut| goes up a layer, so the focus changes to the development containing
the current working location.

> goOut :: ProofState -> ProofState
> goOut (ls :< l, dev) = (ls,
>     (elders l :< E (mother l) (lastName (mother l)) (Girl LETG dev) <>< cadets l
>     ,laytip l
>     ,layroot l))
> goOut (B0, _) = error "goOut: already at outermost layer"


|goUp| moves the focus to the next eldest girl.

> goUp :: ProofState -> ProofState
> goUp = goUpAcc F0
>     where goUpAcc :: Fwd Entry -> ProofState -> ProofState
>           goUpAcc acc (ls :< Layer 
>                        (es :< E newRef _ (Girl LETG newDev)) oldRef@(name := _) cadets tip root
>                       , oldDev)
>               = (ls :< Layer es newRef 
>                    (acc <+> (E oldRef (last name) (Girl LETG oldDev) :> cadets)) tip root
>                 , newDev)
>           goUpAcc acc (ls :< Layer (es :< e) ref cadets tip root, dev)
>               = goUpAcc (e :> acc) (ls :< Layer es ref cadets tip root, dev)
>           goUpAcc _ (_ :< Layer B0 _ _ _ _, _) 
>               = error "goUp: no girls above current development"
>           goUpAcc _ (B0, _)
>               = error "goUp: cannot move up from outermost development"


|goDown| moves the focus to the next youngest girl.

> goDown :: ProofState -> ProofState
> goDown = goDownAcc B0
>     where goDownAcc :: Bwd Entry -> ProofState -> ProofState
>           goDownAcc acc (ls :< l@(Layer elders ref (e :> es) tip root), dev)
>               = case e of
>                     E newRef _ (Girl LETG newDev) ->
>                         (ls :< l{elders=elders:<E ref (lastName ref) (Girl LETG dev) <+> acc,
>                                  mother=newRef, cadets=es}, newDev)
>                     e ->
>                         goDownAcc (acc :< e) (ls :< l{cadets=es}, dev)
>           goDownAcc _ (_ :< Layer _ _ F0 _ _, _) 
>               = error "goDown: no girls below current development"
>           goDownAcc _ (B0,  _)
>               = error "goDown: cannot move down from outermost development"


|appendBinding| and |appendGoal| add entries to the working development,
without type-checking or handling roots properly at the moment.

> appendBinding :: (String :<: TY) -> BoyKind -> ProofState -> ProofState
> appendBinding x k (ls, (es, tip, r)) = 
>     freshRef x (\ref@(n := _) r ->
>                     (ls, (es :< E ref (last n) (Boy k), tip, r))) r

> appendGoal :: (String :<: TY) -> ProofState -> ProofState
> appendGoal (s:<:ty) (ls, (es, tip, root)) = 
>     let n = name root s
>         ref = n := HOLE :<: ty in
>     (ls, (es :< E ref (lastName ref) (Girl LETG (B0, Unknown ty, room root s)), 
>           tip, roos root))


|auncles| calculates the elder aunts or uncles of the current development,
thereby giving a list of entries that are currently in scope.

> auncles :: ProofState -> Bwd Entry
> auncles (ls, (es, _, _)) = foldMap elders ls <+> es


\section{Command-line interface}

|showDev| is an ugly-printer for developments that makes the structure a little
bit clearer than the derived |Show| instance.

> showDev :: Dev -> String
> showDev d = showDevAcc d 0 ""
>     where showDevAcc :: Dev -> Int -> String -> String
>           showDevAcc (B0, t, r) n acc = acc ++ "\n" ++ indent n 
>                                         ++ "Tip: " ++ show t ++ "\n" ++ indent n
>                                         ++ "Root: " ++ show r
>           showDevAcc (es :< E ref _ (Boy k), t, r) n acc = 
>               showDevAcc (es, t, r) n (
>               "\n" ++ indent n ++ "Boy " ++ show k ++ " " ++ show ref
>               ++ acc)
>           showDevAcc (es :< E ref _ (Girl LETG d), t, r) n acc = 
>               showDevAcc (es, t, r) n (
>               "\n" ++ indent n ++ "Girl " ++ show ref
>               ++ showDevAcc d (succ n) ""
>               ++ acc)
>               
>           indent n = replicate (n*4) ' '
                
> printDev :: Dev -> IO ()
> printDev = putStrLn . showDev

> showRef :: REF -> String
> showRef (ns := _) = unwords (fst . unzip $ ns)


Here we have a very basic command-driven interface to the zipper.

> elaborator :: ProofState -> IO ()
> elaborator loc = do
>   printDev (snd loc)
>   case fst loc of
>       _ :< layer  -> putStr ((showRef . mother $ layer) ++ " > ")
>       _       -> putStr "Top > "
>   l <- getLine
>   case words l of
>     "in":_ -> elaborator (goIn loc)
>     "out":_ -> elaborator (goOut loc)
>     "up":_ -> elaborator (goUp loc)
>     "down":_ -> elaborator (goDown loc)
>     "goal":s:_ -> elaborator (appendGoal (s :<: C Set) loc)
>     "bind":s:_ -> elaborator (appendBinding (s :<: C Set) LAMB loc)
>     "auncles":_ -> putStrLn (foldMap ((++"\n").show) (auncles loc)) >> elaborator loc
>     "quit":_ -> return ()
>     _ -> putStrLn "???" >> elaborator loc