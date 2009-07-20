\section{Root}

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Root where

%if False

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
> fresh (x :<: ty) f (r,i) = f (pval (name (r,i) x := DECL ty)) (r,i+1)

> roos :: Root -> Root
> roos (sis, i) = (sis, i + 1)
