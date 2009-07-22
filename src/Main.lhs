> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import Data.Foldable

> import Lexer
> import Layout
> import CoreLoad

> pipe :: String -> String
> pipe = foldMap (foldMap tokOut) . snd . coreLoad . layout . tokenize

> main :: IO ()
> main = interact pipe
