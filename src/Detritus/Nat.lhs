\section{Nat}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Nat where

> import BwdFwd
> import Tm
> import Rules
> import Tactics

%endif

\subsection{Nat in the |Desc| universe}

We define the natural numbers as an inductive data-type in the |Desc|
universe. There are two constructors |natConst|: either |czero| or
|csuc|. In the case of |czero|, we are |Done|: there is no sub-node. In
the case |csuc|, there is one subtree and that's it.

This gives:

> natdTac :: Tac VAL
> natdTac = argTac natEnumTac natcTac
>     where natEnumTac = enumTTac natConst 
>               where natConst = consETac (tagTac "czero")
>                                         (consETac (tagTac "csuc")
>                                                   (nilETac))
>                                            
>           natcTac = switch $ cases [ doneTac
>                                    , ind1Tac doneTac ]

The natural numbers as such are the fix-point of the previous
definition:

> natTac :: Tac VAL
> natTac = muTac natdTac
> nat :: VAL
> nat = trustMe (SET :>: natTac)

\subsection{Natural number constructors}

Hence, we have the standard constructors of natural numbers. Let start
with |zero|:

> zeroTac :: Tac VAL
> zeroTac = conTac $ cases [ zeTac ]

\question{Honestly, I would not have written that, so I don't know
          how/why this thing works. I cannot link that definition with
          the one I wrote in the Agda model.}

Similarly, we can implement the |suc| constructor:

> sucTac :: Tac VAL -> Tac VAL
> sucTac x = conTac $ cases [ suTac zeTac
>                           , x ]

\question{Same as above.}

So, at this stage, we have regained the constructors of natural
numbers. Therefore, we can already do some \emph{crazy} stuffs! Let's
go wild and write 2! 

> two :: VAL
> two = trustMe (nat :>: twoTac) 
>       where twoTac = sucTac $ 
>                      sucTac $ 
>                      zeroTac

However, I'm more than crazy, I'm desperate. So, I'll write 4, yeah!

> four :: VAL
> four = trustMe (nat :>: fourTac)
>     where fourTac = sucTac $ 
>                     sucTac $ 
>                     sucTac $ 
>                     sucTac $ 
>                     zeroTac

\subsection{Addition}

The definition of the sum is\ldots \emph{haha}\ldots a mystery. The
idea is to use the |foldDesc| eliminator of |Mu| to fold over
|n1|. When reaching |zero|, we return |n2|. Otherwise, we go deeper,
applying the precept saying that |n1 + n2 = suc ((n1 - 1) + n2)|.

> plus :: VAL
> plus = trustMe (plusType :>: plusTac)
>     where plusTac = lambda $ \n2 ->
>                     foldDesc $
>                     split $ 
>                     switch $ 
>                     cases [ lambda $ \_ ->
>                             lambda $ \_ ->
>                             use n2 done
>                           , lambda $ \_ ->
>                             lambda $ \ih -> 
>                             sucTac $ 
>                             use ih . 
>                             apply Fst $
>                             done ]
>           plusType = ARR nat (ARR nat nat)


\question{Just as above, I'm a bit confused by the first |lambda|
          required in both cases. Apart from that, I'm happy to find
          the definition I had in Agda.}

I'm quite sure that you're holding your breath, wondering "will 2 + 2
equal 4?". Last time I checked, it did. 

> twoTwo = plus $$ A two $$ A two


\subsection{OTT in action}

Real men are able to inhabit this type. I'm kind of short of
testosterone these days, so I let this as an exercise to the reader.

> lemTy :: VAL
> lemTy = PRF $ eval [.plus.zero.nat2nat. 
>           eqGreen :@ [NV nat2nat
>                      ,L $ "" :. [.n. N $ V plus :$ A (NV n) :$ A (NV zero)]
>                      ,NV nat2nat
>                      ,L $ "" :. [.n. N $ V plus :$ A (NV zero) :$ A (NV n)]
>                      ]] $ B0 :< plus :< zero :< nat2nat
>         where nat2nat = ARR nat nat
>               zero = trustMe (nat :>: zeroTac)