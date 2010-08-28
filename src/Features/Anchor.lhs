\section{Anchors}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Anchor where

%endif


infixr 5 _∷_

data AllowedBy : Set -> Set where
  ε    : forall {T} -> 
         AllowedBy T
  _∷_  : {S : Set}{T : S -> Set} -> 
         (s : S)(ts : AllowedBy (T s)) -> AllowedBy ((x : S) -> T x)

UId = String

-- The universe (that's a tiny one):

data Label : Set where
  label : (u : UId)(T : Set)(ts : AllowedBy T) -> Label


\subsection{Plugging in canonical forms}

> import -> CanConstructors where
>     Anchors  ::  Can t
>     Anchor   ::  t -> t -> t -> Can t
>     AllowedBy :: t -> Can t
>     AllowedEpsilon :: Can t
>     AllowedCons :: t -> t -> t -> t -> t -> Can t

> import -> CanTyRules where
>     canTy chev (Set :>: Anchors) = return Anchors
>     canTy chev (Anchors :>: Anchor u t ts) = do
>         uuv <- chev (UID :>: u)
>         ttv@(t :=>: tv) <- chev (SET :>: t)
>         tstsv <- chev (ALLOWEDBY tv :>: ts)
>         return $ Anchor uuv ttv tstsv
>     canTy chev (Set :>: AllowedBy t) = do
>         ttv <- chev (SET :>: t)
>         return $ AllowedBy ttv
>     canTy chev (AllowedBy t :>: AllowedEpsilon) = do
>         return $ AllowedEpsilon
>     canTy chev (AllowedBy ty :>: AllowedCons _S _T q s ts) = do
>         _SSv@(_S :=>: _Sv) <- chev (SET :>: _S)
>         _TTv@(_T :=>: _Tv) <- chev (ARR _Sv SET :>: _T)
>         qqv <- chev (PRF (EQBLUE (SET :>: ty) (SET :>: PI _Sv _Tv)) :>: q)
>         ssv@(s :=>: sv) <- chev (_Sv :>: s)
>         tstsv <- chev (ALLOWEDBY (_Tv $$ (A sv)) :>: ts)
>         return $ AllowedCons _SSv _TTv qqv ssv tstsv

> import -> CanCompile where
>     {- empty -}

> import -> CanEtaExpand where
>     {- empty -}

> import -> CanPats where
>     pattern ANCHORS        = C Anchors
>     pattern ANCHOR u t ts  = C (Anchor u t ts)
>     pattern ALLOWEDBY t    = C (AllowedBy t)
>     pattern ALLOWEDEPSILON t = C (AllowedEpsilon t)
>     pattern ALLOWEDCONS _S _T q s ts = C (AllowedCons _S _T q s ts) 

> import -> CanDisplayPats where
>     {- empty -}

> import -> CanPretty where
>     {- Not yet implemented -}

> import -> CanTraverse where
>     traverse _ Anchors = (| Anchors |)
>     traverse f (Anchor u t ts) = (|Anchor (f u) (f t) (f ts)|)
>     {- To be continued -}

> import -> CanHalfZip where
>     halfZip Anchors Anchors = Just Anchors
>     halfZip (Anchor u1 t1 ts1) (Anchor u2 t2 ts2) = Just $ Anchor (u1, u2) (t1, t2) (ts1, ts2)
>     {- To be continued -}

\subsection{Plugging in eliminators}

> import -> ElimTyRules where
>     {- empty -}

> import -> ElimComputation where
>     {- empty -}

> import -> ElimCompile where
>     {- empty -}

> import -> ElimTraverse where
>     {- empty -}

> import -> ElimPretty where
>     {- empty -}

\subsection{Plugging in operators}

> import -> Operators where
>     {- empty -}

> import -> OpCompile where
>     {- empty -}

> import -> OpCode where
>     {- empty -}

\subsection{Plugging in axioms and primitives}

> import -> RulesCode where
>     {- empty -}

> import -> Primitives where

\subsection{Extending the type-checker}

> import -> Check where
>     {- mepty -}

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where

\subsection{Extending the display language}

> import -> DInTmConstructors where

> import -> DInTmTraverse where

> import -> DInTmPretty where

> import -> Pretty where

\subsection{Extending the concrete syntax}

> import -> KeywordConstructors where

> import -> KeywordTable where

> import -> ElimParsers where

> import -> DInTmParsersSpecial where

> import -> DInTmParsersMore where

> import -> ParserCode where

\subsection{Extending the elaborator and distiller}

> import -> MakeElabRules where
 
> import -> DistillRules where

