\section{Features}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

%endif

> module Features.Features where

This module should import all the feature modules. This module
should be imported by all the functionality modules. This module
thus functions as exactly the list of features included in the
current version of the system.

> import Features.UId        ()
> import Features.Enum       ()
> import Features.Sigma      ()
> import Features.Problem    ()
> import Features.Prop       ()
> import Features.Desc       ()
> import Features.IDesc      ()
> import Features.Equality   ()
> import Features.Nu         ()
> import Features.Labelled   ()
> import Features.Quotient   ()
> import Features.FreeMonad  ()
> import Features.Record     ()
> import Features.Anchor     ()

