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

Yes! Equality is only meaningful when the sets are equal.

< eqGreen(Prf _, _, Prf _, _) :-> Trivial

> import -> CanConstructors where
>   Prop    :: Can t
>   Prf     :: t -> Can t
>   All     :: t -> t -> Can t
>   And     :: t -> t -> Can t
>   Trivial :: Can t
>   Absurd  :: Can t
>   Box     :: Irr t -> Can t
>   Inh     :: t -> Can t
>   Wit     :: t -> Can t

Elim forms inherited from elsewhere

> import -> TraverseCan where
>   traverse _ Prop      = (|Prop|)
>   traverse f (Prf p)   = (|Prf (f p)|)
>   traverse f (All p q) = (|All (f p) (f q)|)
>   traverse f (And p q) = (|And (f p) (f q)|)
>   traverse _ Trivial   = (|Trivial|)
>   traverse _ Absurd    = (|Absurd|)
>   traverse f (Box p)   = (|Box (traverse f p)|)
>   traverse f (Inh ty)  = (|Inh (f ty)|)
>   traverse f (Wit t)   = (|Wit (f t)|)

> import -> HalfZipCan where
>   halfZip  Prop      Prop      = Just Prop
>   halfZip  (Prf p0)  (Prf p1)  = Just (Prf (p0, p1))

> import -> CanPats where
>   pattern PROP        = C Prop
>   pattern PRF p       = C (Prf p)
>   pattern ALL p q     = C (All p q)
>   pattern IMP p q     = ALL (PRF p) (L (K q))
>   pattern ALLV x s p  = ALL s (LAV x p)
>   pattern AND p q     = C (And p q)
>   pattern TRIVIAL     = C Trivial
>   pattern ABSURD      = C Absurd
>   pattern BOX p       = C (Box p)
>   pattern INH ty      = C (Inh ty)
>   pattern WIT t       = C (Wit t)

> import -> DisplayCanPats where
>   pattern DPROP        = DC Prop
>   pattern DPRF p       = DC (Prf p)
>   pattern DALL p q     = DC (All p q)
>   pattern DIMP p q     = DALL (DPRF p) (DL (DK q))
>   pattern DALLV x s p  = DALL s (DLAV x p)
>   pattern DAND p q     = DC (And p q)
>   pattern DTRIVIAL     = DC Trivial
>   pattern DABSURD      = DC Absurd
>   pattern DBOX p       = DC (Box p)

> import -> SugarTactics where
>   propTac = can Prop
>   prfTac p = can $ Prf p
>   impTac p q = can $ All (can $ Prf p)
>                          (lambda $ \_ -> q)
>   allTac p q = can $ All p (lambda q)
>   andTac p q = can $ And p q
>   trivialTac = can Trivial
>   absurdTac = can Absurd
>   boxTac t = can $ Box t

> import -> CanPretty where
>   pretty Prop           = text "#"
>   pretty (Prf p)        = parens (text ":-" <+> pretty p)
>   pretty (All p q)      = parens (text "All" <+> pretty p <+> pretty q)
>   pretty (And p q)      = parens (pretty p <+> text "&&" <+> pretty q)
>   pretty Trivial        = text "TT"
>   pretty Absurd         = text "FF"
>   pretty (Box (Irr p))  = parens (text "Box" <+> pretty p)

> import -> CanTyRules where
>   canTy _   (Set :>: Prop) = return Prop
>   canTy chev  (Set :>: Prf p) = (|Prf (chev (PROP :>: p))|)
>   canTy chev  (Prop :>: All s p) = do
>     ssv@(_ :=>: sv) <- chev (SET :>: s)
>     ppv <- chev (ARR sv PROP :>: p)
>     return $ All ssv ppv
>   canTy chev  (Prop :>: And p q) = 
>     (|And (chev (PROP :>: p)) (chev (PROP :>: q))|)
>   canTy _  (Prop :>: Trivial) = return Trivial
>   canTy _   (Prop :>: Absurd) = return Absurd
>   canTy chev  (Prf p :>: Box (Irr x)) = (|(Box . Irr) (chev (PRF p :>: x))|)
>   canTy chev (Prf (AND p q) :>: Pair x y) = do
>     (|Pair (chev (PRF p :>: x)) (chev (PRF q :>: y))|)
>   canTy _   (Prf TRIVIAL :>: Void) = return Void
>   canTy chev (Prop :>: Inh ty) = (|Inh (chev (SET :>: ty))|)
>   canTy chev (Prf (INH ty) :>: Wit t) = (|Wit (chev (ty :>: t))|)

> import -> ElimTyRules where
>   elimTy chev (f :<: Prf (ALL p q))      (A e)  = do
>     eev@(e :=>: ev) <- chev (p :>: e)
>     return $ (A eev, PRF (q $$ A ev))
>   elimTy chev (_ :<: Prf (AND p q))      Fst    = return (Fst, PRF p)
>   elimTy chev (_ :<: Prf (AND p q))      Snd    = return (Snd, PRF q)

> import -> OpCode where
>   nEOp = Op { opName = "naughtE"
>             , opArity = 2
>             , opTyTel =  "z" :<: PRF ABSURD :-: \ _ ->
>                          "X" :<: SET :-: \ xX -> Ret xX
>             , opRun = \ [q, ty] -> case q of
>                 N z -> Left z
>                 v -> error ("oh bugger: " ++ show v)
>             , opSimp = \_ _ -> empty
>             }
>   inhEOp = Op { opName = "inhOp"
>               , opArity = 4
>               , opTyTel = "S" :<: SET :-: \ ty ->
>                           "p" :<: PRF (INH ty) :-: \ p ->
>                           "P" :<: IMP (PRF (INH ty)) PROP :-: \ pred ->
>                           "m" :<: PI ty (L $ HF "s" $ \ t -> 
>                                            pred $$ A (WIT t)) :-: \ _ -> 
>                           Ret (PRF (pred $$ A p))
>               , opRun = \[_,p,_,m] -> case p of
>                                         WIT t -> Right $ m $$ A t
>                                         N n   -> Left n
>               , opSimp = \_ _ -> empty
>               }

> import -> Operators where
>   nEOp :
>   inhEOp :

> import -> EtaExpand where
>   etaExpand (Prf p :>: x) r = Just (BOX (Irr (inQuote (PRF p :>: x) r)))

> import -> Check where
>   check (PRF (ALL p q) :>: L sc)  = do
>     Rooty.freshRef ("" :<: p)
>       (\ref -> check (PRF (q $$ A (pval ref)) :>: underScope sc ref))
>     return $ () :=>: (evTm $ L sc)

> import -> OpRunEqGreen where
>   opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
>   opRunEqGreen [PRF _,_,PRF _,_] = Right TRIVIAL

> import -> Coerce where
>   coerce Prop              q pP  = Right pP
>   coerce (Prf (pP1, pP2))  q p   = Right $ q $$ Fst $$ A p

