\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Prop where

%endif

\question{Do the Formation/Introduction/\ldots names make sense?}
\question{How to handle the eliminators?}
\question{Eta expansion?}

Formation rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{Prop-formation}
\UnaryInfC{|Set :>: Prop|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Prop :>: p|}
\RightLabel{Prf-formation}
\UnaryInfC{|Set :>: Prf p|}
\end{prooftree}

Introduction rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{Prop-intro-1}
\UnaryInfC{|Prop :>: Trivial|}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\RightLabel{Prop-intro-2}
\UnaryInfC{|Prop :>: Absurd|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Set :>: S|}
\AxiomC{|S -> Set :>: P|}
\RightLabel{Prop-intro-3}
\BinaryInfC{|Prop :>: All S P|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Prop :>: p|}
\AxiomC{|Prop :>: q|}
\RightLabel{Prop-intro-4}
\BinaryInfC{|Prop :>: And p q|}
\end{prooftree}

\question{Is that our proof irrelevance?}

\begin{prooftree}
\AxiomC{|p :>: x|}
\RightLabel{Prf-intro-1}
\UnaryInfC{|Prf p :>: Box (Irr x)|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Prf p :>: x|}
\AxiomC{|Prf q :>: y|}
\RightLabel{And-intro}
\BinaryInfC{|And p q :>: Pair x y|}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\RightLabel{Trivial-intro}
\UnaryInfC{|Trivial :>: Void|}
\end{prooftree}

Elimination rules:

\begin{prooftree}
\AxiomC{|Prf Absurd :>: z|}
\AxiomC{|Set :>: ty|}
\RightLabel{naughtE-elim}
\BinaryInfC{|ty :>: naughtE z ty|}
\end{prooftree}

With no computational rule (!)

Equality rules:

< eqGreen(Prop, t1, Prop, t2) :-> And (Imp t1 t2) (Imp t2 t1)

\question{Can we really say that all terms of any proofs are equal?
          Even if they are terms of distinct proofs?}

< eqGreen(Prf _, _, Prf _, _) :-> Trivial

> import -> CanConstructors where
>   Prop    :: Can t
>   Prf     :: t -> Can t
>   All     :: t -> t -> Can t
>   And     :: t -> t -> Can t
>   Trivial :: Can t
>   Absurd  :: Can t
>   Box     :: Irr t -> Can t

Elim forms inherited from elsewhere

> import -> TraverseCan where
>   traverse _ Prop      = (|Prop|)
>   traverse f (Prf p)   = (|Prf (f p)|)
>   traverse f (All p q) = (|All (f p) (f q)|)
>   traverse f (And p q) = (|And (f p) (f q)|)
>   traverse _ Trivial   = (|Trivial|)
>   traverse _ Absurd    = (|Absurd|)
>   traverse f (Box p)   = (|Box (traverse f p)|)

> import -> CanPats where
>   pattern PROP    = C Prop
>   pattern PRF p   = C (Prf p)
>   pattern IMP p q = C (All (PRF p) (L (K q)))
>   pattern ALL p q = C (All p q)
>   pattern AND p q = C (And p q)
>   pattern TRIVIAL = C Trivial
>   pattern ABSURD  = C Absurd
>   pattern BOX p   = C (Box p)

> import -> CanPretty where
>   prettyCan Prop           = text "#"
>   prettyCan (Prf p)        = parens (text ":-" <+> pretty p)
>   prettyCan (All p q)      = parens (text "All" <+> pretty p <+> pretty q)
>   prettyCan (And p q)      = parens (pretty p <+> text "&&" <+> pretty q)
>   prettyCan Trivial        = text "TT"
>   prettyCan Absurd         = text "FF"
>   prettyCan (Box (Irr p))  = parens (text "Box" <+> pretty p)

> import -> SugarTactics where
>   impTac p q = can $ All (can $ Prf p)
>                          (lambda $ \_ -> q)

> import -> CanTyRules where
>   canTy _   (Set :>: Prop)           = return Prop
>   canTy chev  (Set :>: Prf p)         = do
>     ppv@(p :=>: pv) <- chev (PROP :>: p)
>     return $ Prf ppv
>   canTy chev  (Prop :>: All s p)       = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ppv@(p :=>: pv) <- chev (ARR sv PROP :>: p)
>     return $ All ssv ppv
>   canTy chev  (Prop :>: And p q)       = do
>     ppv@(p :=>: pv) <- chev (PROP :>: p)
>     qqv@(q :=>: qv) <- chev (PROP :>: q)
>     return $ And ppv qqv
>   canTy _  (Prop :>: Trivial)       = return Trivial
>   canTy _   (Prop :>: Absurd)        = return Absurd
>   canTy chev  (Prf p :>: Box (Irr x))  = do
>     xxv@(x :=>: xv) <- chev (PRF p :>: x)
>     return $ Box (Irr (xxv))
>   canTy chev (Prf (AND p q) :>: Pair x y)   = do
>     xxv@(x :=>: xv) <- chev (PRF p :>: x)
>     yyv@(y :=>: yv) <- chev (PRF q :>: y)
>     return $ Pair xxv yyv
>   canTy _   (Prf TRIVIAL :>: Void)       = return Void


> import -> ElimTyRules where
>   elimTy chev (f :<: Prf (ALL p q))      (A e)  = do
>     eev@(e :=>: ev) <- chev (p :>: e)
>     return $ (A eev, PRF (q $$ A ev))
>   elimTy chev (_ :<: Prf (AND p q))      Fst    = return (Fst, PRF p)
>   elimTy chev (_ :<: Prf (AND p q))      Snd    = return (Snd, PRF q)

> import -> OpCode where
>   nEOp = Op { opName = "naughtE"
>             , opArity = 2
>             , opTy = opty
>             , opRun = oprun
>             } where
>               opty chev [z,ty] = do
>                    (z :=>: zv) <- chev (PRF ABSURD :>: z)
>                    (ty :=>: tyv) <- chev (SET :>: ty)
>                    return ([ z :=>: zv
>                            , ty :=>: tyv ]
>                           , tyv)
>               opty _ _      = traceErr "naughtE: invalid arguments"
>               oprun :: [VAL] -> Either NEU VAL
>               oprun [N z,ty] = Left z

> import -> Operators where
>   nEOp :

> import -> EtaExpand where
>   etaExpand (PRF p :>: x) r = Just (BOX (Irr (bquote B0 x r)))

> import -> Check where
>   check (PRF (ALL p q) :>: L sc) r = do
>     Root.freshRef ("" :<: p)
>       (\ref -> check (PRF (q $$ A (pval ref)) :>: underScope sc ref))
>       r

> import -> OpRunEqGreen where
>   opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
>   opRunEqGreen [PRF _,_,PRF _,_] = Right TRIVIAL
