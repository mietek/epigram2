\section{Root}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Root where

> import Data.Foldable
> import Control.Monad
> import Control.Applicative

> import BwdFwd
> import Tm

%endif

> type Root = (Bwd (String, Int), Int)

> name :: Root -> String -> Name
> name (sis, i) s = trail (sis :< (s, i))

> fresh :: (String :<: VAL) -> (VAL -> Root -> t) -> Root -> t
> fresh (x :<: ty) f r = f (pval (name r x := DECL ty)) (roos r)

> roos :: Root -> Root
> roos (sis, i) = (sis, i + 1)

> room :: Root -> String -> Root
> room (sis, i) s = (sis :< (s,i), 0)