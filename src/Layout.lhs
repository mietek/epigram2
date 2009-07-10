\section{Layout}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE RelaxedPolyRec, TypeSynonymInstances #-}

> module Layout where

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Char
> import Data.List
> import Control.Arrow (first)

> import Lexer

%endif

> layout :: [(Int, Tok)] -> [[Tok]]
> layout its = unl . execWriter $ evalStateT layoutL its

> layoutL :: L Lines ()
> layoutL = lBody (-1) maxBound False

> braToks :: Monoid x => Br -> L x [Tok]
> braToks b = do
>   (mb, ts) <- local $ bBody b
>   case mb of
>     Just b' -> (|[B b ts b']|)
>     Nothing -> (|(Ope b : ts)|)

> layToks :: Monoid x => String -> Int -> L x [Tok]
> layToks k i = do
>  ((), l) <- local $ lBody i maxBound False
>  (|[L k (unl l)]|)

> bBody :: Br -> L [Tok] (Maybe Br)
> bBody o = look . next (|Left ~ Nothing|) $ \ _ t -> case t of
>   Clo c  | brackets o c  -> (|Right ~ (|Just ~ c|)|)
>          | otherwise     -> (|Left ~ Nothing|)
>   Ope b -> (|{tell =<< braToks b} Right ~ (bBody o)|)
>   K k | elem k lakeys -> (|{tell =<< layToks k (-1)} Right ~ (bBody o)|)
>   t -> tell [t] >> (|Right ~ (bBody o)|)

> lBody :: Int -> Int -> Bool -> L Lines ()
> lBody i j b = look $ space $ \ ss -> next (|Left ~ ()|) $ \ k t -> case t of
>   _ | k <= i -> (|Left ~ ()|)
>   Clo _ -> (|Left ~ ()|)
>   Sem -> do
>     if b then tell brk else (|()|)
>     tell $ cur ss
>     tell $ cur [t]
>     (|Right ~ (lBody i (min j k) False)|)
>   t -> let n = k <= j ; j' = if n then k else j in do
>       if (b && n) then tell brk else (|()|)
>       tell $ cur ss
>       if n then tell brk else (|()|)
>       case t of
>         Ope b                -> tell =<< (|cur (braToks b)|)
>         K w | elem w lakeys  -> tell =<< (|cur (layToks w j)|)
>         _                    -> tell $ cur [t]
>       (|Right ~ (lBody i j' True)|)

> lakeys :: [String]
> lakeys = ["where"]


> type L x = StateT [(Int, Tok)] (Writer x)
> instance Monoid x => Applicative (L x) where
>   pure = return
>   (<*>) = ap

> newtype Lines = Lines {unl :: [[Tok]]} -- non-empty
> instance Monoid Lines where
>   mempty = Lines [[]]
>   mappend (Lines [xs]) (Lines (ys : yss)) = Lines ((xs ++ ys) : yss)
>   mappend (Lines (xs : xss)) y = Lines (xs : unl (mappend (Lines xss) y))

> brk :: Lines
> brk = Lines [[], []]

> cur :: [Tok] -> Lines
> cur ts = Lines [ts]

> local :: Monoid x => L y a -> L x (a, y)
> local l = do
>   s <- get
>   let w = runStateT l s
>   let ((a, s'), y) = runWriter w
>   put s'
>   return (a, y)

> look :: Monoid x => L x (Either a (L x a)) -> L x a
> look l = do
>   s <- get
>   q <- l
>   case q of
>     Left a -> put s >> return a
>     Right l -> l

> space :: Monoid x => ([Tok] -> L x a) -> L x a
> space f = do
>   its <- get
>   let (iss, ius) = span (isSpcT . snd) its
>   put ius
>   f (map snd iss)

> next :: Monoid x => L x a -> (Int -> Tok -> L x a) -> L x a
> next n f = do
>   its <- get
>   case its of
>     []            -> n
>     (i, t) : its  -> put its >> f i t
