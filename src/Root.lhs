\section{Root}

> module Root where

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> import Data.Foldable
> import Control.Monad
> import Control.Applicative

> import BwdFwd
> import Tm

%endif

> type Root = (Bwd (String, Int), Int)

> name :: Root -> String -> Name
> name (sis, i) s = trail (sis :< (s, i))

> roos :: Root -> Root
> roos (sis, i) = (sis, i + 1)