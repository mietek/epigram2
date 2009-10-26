\section{Dev Zipper}

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

%if False

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
>                
> printDev :: Dev -> IO ()
> printDev = putStrLn . showDev

%endif

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

The current state is then represented by a stack of |Layer|s, along with the
current working development:

> type WhereAmI = (Bwd Layer, Dev)

Now we need functions to manipulate the unzipped data structure.

|goIn| changes the current location to the bottom-most girl in the current development.

> goIn :: WhereAmI -> WhereAmI
> goIn l = goInAcc l F0 
>     where goInAcc :: WhereAmI -> Fwd Entry -> WhereAmI
>           goInAcc (ls, (es :< E ref (s, _) (Girl LETG dev), tip, root)) cadets
>               = (ls :< Layer es ref cadets tip root, dev)
>           goInAcc (ls, (es :< e, tip, root)) cadets
>               = goInAcc (ls, (es, tip, root)) (e :> cadets)
>           goInAcc (_, (B0, _, _)) _ = error "goIn: no girls in current development"


|goOut| goes up a layer, so the focus changes to the development containing
the current working location.

> goOut :: WhereAmI -> WhereAmI
> goOut (ls :< Layer elders ref@(name := _) cadets tip root, dev)
>     = (ls, (elders :< E ref (last name) (Girl LETG dev) <>< cadets, tip, root))
> goOut (B0, _) = error "goOut: already at outermost layer"


|goUp| moves the focus to the next eldest girl.

> goUp :: WhereAmI -> WhereAmI
> goUp = goUpAcc F0
>     where goUpAcc :: Fwd Entry -> WhereAmI -> WhereAmI
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

> goDown :: WhereAmI -> WhereAmI
> goDown = goDownAcc B0
>     where goDownAcc :: Bwd Entry -> WhereAmI -> WhereAmI
>           goDownAcc acc (ls :< Layer 
>                        elders oldRef@(name := _) (E newRef _ (Girl LETG newDev) :> cadets) tip root
>                       , oldDev)
>               = (ls :< Layer 
>                  ((elders :< E oldRef (last name) (Girl LETG oldDev)) <+> acc) newRef cadets tip root
>                 , newDev)
>           goDownAcc acc (ls :< Layer elders ref (e :> es) tip root, dev)
>               = goDownAcc (acc :< e) (ls :< Layer elders ref es tip root, dev)
>           goDownAcc _ (_ :< Layer _ _ F0 _ _, _) 
>               = error "goDown: no girls below current development"
>           goDownAcc _ (B0,  _)
>               = error "goDown: cannot move down from outermost development"


|appendBinding| and |appendGoal| add entries to the working development,
without type-checking or handling roots properly at the moment.

> appendBinding :: (String :<: TY) -> BoyKind -> WhereAmI -> WhereAmI
> appendBinding x k (ls, (es, tip, r)) = 
>     freshRef x (\ref@(n := _) r ->
>                     (ls, (es :< E ref (last n) (Boy k), tip, r))) r

> appendGoal :: (String :<: TY) -> WhereAmI -> WhereAmI
> appendGoal (s:<:ty) (ls, (es, tip, root)) = 
>     let n = name root s in
>     (ls, (es :< E (n := HOLE :<: ty) (last n) (Girl LETG (B0, Unknown ty, room root s)), tip, roos root))


|auncles| calculates the elder aunts or uncles of the current development,
thereby giving a list of entries that are currently in scope.

> auncles :: WhereAmI -> Bwd Entry
> auncles (ls, (es, _, _)) = foldMap elders ls <+> es