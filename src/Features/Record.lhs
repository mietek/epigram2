\section{Records feature}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Record where

%endif


\subsection{Plugging in canonical forms}

> import -> CanConstructors where
>   Record  :: Labelled Id t -> Can t
>   REmpty  :: Can t
>   RCons   :: t -> t -> t -> Can t
>   RSig    :: Can t

> import -> CanTyRules where
>   canTy chev (Set :>: RSig)  = do
>     return $ RSig
>   canTy chev (RSig :>: REmpty) = do
>     return $ REmpty
>   canTy chev (RSig :>: RCons sig id ty) = do
>     ssv@(s :=>: sv) <- chev (RSIG :>: sig)
>     iiv@(i :=>: iv) <- chev (UID :>: id)
>     ttv@(t :=>: tv) <- chev (ARR (recordOp @@ [sv]) SET  :>: ty)
>     return $ RCons ssv iiv ttv
>   canTy chev (Set :>: Record (ml :?=: Id r)) = do
>     mlv <- traverse (chev . (SET :>:)) ml
>     rrv@(r :=>: rv) <- chev (RSIG :>: r)
>     return $ Record (mlv :?=: Id rrv)
>   canTy chev (tv@(Record (_ :?=: Id x)) :>: Con y) = do
>     yyv@(y :=>: yv) <- chev (recordOp @@ [x] :>: y)
>     return $ Con yyv


> import -> CanCompile where
>     -- XXX: Not yet implemented

> import -> CanEtaExpand where
>     etaExpand (Record (_ :?=: Id REMPTY) :>: v) r = Just $ CON UNIT
>     etaExpand (Record (_ :?=: Id (RCONS sig i ty)) :>: p) r =
>         -- XXX: to be implemented
>         undefined

> import -> CanPats where
>   pattern RSIG         = C RSig
>   pattern REMPTY       = C REmpty
>   pattern RCONS s i t  = C (RCons s i t)
>   pattern RECORD l s   = C (Record (l :?=: Id s))

> import -> CanDisplayPats where
>   pattern DRSIG         = DC RSig
>   pattern DREMPTY       = DC REmpty
>   pattern DRCONS s i t  = DC (RCons s i t)
>   pattern DRECORD l s   = DC (Record (l :?=: Id s))

> import -> CanPretty where
>   pretty RSig              =  const $ text "RSignature"
>   pretty REmpty            =  const $ text "empty"
>   pretty (RCons s i t)     =  const $
>                               pretty s ArgSize <+> char '>' 
>                               <+> pretty i ArgSize <+> colon 
>                               <+> pretty t ArgSize 

> import -> CanTraverse where
>   traverse f RSig           = (|RSig|)
>   traverse f REmpty         = (|REmpty|)
>   traverse f (RCons s i t)  = (|RCons (f s) (f i) (f t)|) 

> import -> CanHalfZip where
>   halfZip RSig              RSig              = Just RSig
>   halfZip REmpty            REmpty            = Just REmpty
>   halfZip (RCons s0 i0 t0)  (RCons s1 i1 t1)  =
>     Just (RCons (s0,s1) (i0,i1) (t0,t1))

\subsection{Plugging in eliminators}

> import -> ElimTyRules where
>     -- None

> import -> ElimComputation where
>     -- None

> import -> ElimCompile where
>     -- None

> import -> ElimTraverse where
>     -- None

> import -> ElimPretty where
>     -- None

\subsection{Plugging in operators}

> import -> Operators where
>   recordOp :
>   labelsOp :
>   typeAtOp :
>   fstsOp :
>   atOp :

> import -> OpCompile where
>     -- XXX: Not yet implemented

> import -> OpCode where
>   recordOp = Op 
>     { opName   = "Record"
>     , opArity  = 1
>     , opTyTel  = recordOpTy
>     , opRun    = recordOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         recordOpTy = "sig" :<: RSIG :-: \sig ->
>                      Target SET
>         recordOpRun :: [VAL] -> Either NEU VAL
>         recordOpRun [REMPTY]           = Right UNIT
>         recordOpRun [RCONS sig id ty]  = Right $ SIGMA (recordOp @@ [sig]) ty
>         recordOpRun [N x]              = Left x
>
>   labelsOp = Op
>     { opName   = "labels"
>     , opArity  = 1
>     , opTyTel  = labelsOpTy
>     , opRun    = labelsOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         labelsOpTy =  "sig" :<: RSIG :-: \sig ->
>                       Target enumU
>         labelsOpRun :: [VAL] -> Either NEU VAL
>         labelsOpRun [REMPTY]           = Right NILE
>         labelsOpRun [RCONS sig id ty]  = Right $ CONSE id (labelsOp @@ [sig])
>         labelsOpRun [N x]              = Left x
>   
>   typeAtOp = Op
>     { opName   = "typeAt"
>     , opArity  = 2
>     , opTyTel  = typeAtOpTy
>     , opRun    = typeAtOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         typeAtOpTy =  "sig" :<: RSIG :-: \sig ->
>                       "labels" :<: ENUMT (labelsOp @@ [sig]) :-: \_ ->
>                       Target $ SIGMA RSIG  (L $ "S" :. [.s. 
>                                            ARR (N $ recordOp :@ [NV s]) SET])
>         typeAtOpRun :: [VAL] -> Either NEU VAL
>         typeAtOpRun [REMPTY, _]              = 
>             error "typeAt: impossible call on Empty"
>         typeAtOpRun [RCONS sig id ty, ZE]    = Right $ PAIR sig ty
>         typeAtOpRun [RCONS sig id ty, SU n]  = Right $ typeAtOp @@ [ sig, n ]
>         typeAtOpRun [_,N x]                 = Left x
> 
>   fstsOp = Op
>     { opName   = "fsts"
>     , opArity  = 3
>     , opTyTel  = fstsOpTy
>     , opRun    = fstsOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         fstsOpTy =  "sig" :<: RSIG :-: \sig ->
>                     "labels" :<: ENUMT (labelsOp @@ [sig]) :-: \l ->
>                     "rec" :<: recordOp @@ [sig] :-: \_ ->
>                       Target $ recordOp @@ [ typeAtOp @@ [ sig, l ] $$ Fst ]
>         fstsOpRun :: [VAL] -> Either NEU VAL
>         fstsOpRun [REMPTY, _, _]              = 
>             error "fsts: impossible call on Empty"
>         fstsOpRun [RCONS sig id ty, ZE, x]    =
>             Right $ x $$ Fst
>         fstsOpRun [RCONS sig id ty, SU n, x]  =
>             Right $ fstsOp @@ [sig, n, x $$ Fst]
>         fstsOpRun [_, N x, _]                 = Left x
> 
>   atOp = Op
>     { opName   = "at"
>     , opArity  = 3
>     , opTyTel  = atOpTy
>     , opRun    = atOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         atOpTy =  "sig" :<: RSIG :-: \sig ->
>                   "labels" :<: ENUMT (labelsOp @@ [sig]) :-: \l ->
>                   "rec" :<: recordOp @@ [sig] :-: \rec ->
>                    Target $ typeAtOp @@ [ sig, l ] 
>                               $$ Snd 
>                               $$ A (fstsOp @@ [ sig, l, rec])
>         atOpRun :: [VAL] -> Either NEU VAL
>         atOpRun [REMPTY, _, _]              = 
>             error "at: impossible call on Empty"
>         atOpRun [RCONS sig id ty, ZE, x]    =
>             Right $ x $$ Snd
>         atOpRun [RCONS sig id ty, SU n, x]  =
>             Right $ atOp @@ [sig, n, x $$ Fst]
>         atOpRun [_, N x, _]                 = Left x

\subsection{Plugging in axioms and primitives}

> import -> RulesCode where
>     -- None

> import -> Primitives where
>     -- None

\subsection{Extending the type-checker}

> import -> Check where
>     -- None

\subsection{Extending the equality}

> import -> OpRunEqGreen where
>     -- None

> import -> Coerce where
>     -- XXX: not yet implemented 

\subsection{Extending the display language}

> import -> DInTmConstructors where
>     -- None

> import -> DInTmTraverse where
>     -- None

> import -> DInTmPretty where
>     -- None

> import -> Pretty where
>     -- None

\subsection{Extending the concrete syntax}

> import -> KeywordConstructors where
>     KwRecord :: Keyword
>     KwRSig :: Keyword
>     KwREmpty :: Keyword
>     KwRCons :: Keyword

> import -> KeywordTable where
>   key KwRecord        = "Rec"
>   key KwRSig          = "RSig"
>   key KwREmpty        = "REmpty"
>   key KwRCons         = "RCons"


> import -> ElimParsers where
>     -- None

> import -> DInTmParsersSpecial where
>   (AndSize, (|(DRECORD Nothing) (%keyword KwRecord%) (sizedDInTm ArgSize)|)) :
>   (ArgSize, (|(DRSIG) (%keyword KwRSig%) |)) :
>   (ArgSize, (|(DREMPTY) (%keyword KwREmpty%)|)) :
>   (ArgSize, (|(DRCONS) (%keyword KwRCons%) (sizedDInTm ArgSize) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :


> import -> DInTmParsersMore where
>     -- None

> import -> ParserCode where
>     -- None

\subsection{Extending the elaborator and distiller}

> import -> MakeElabRules where
>     -- Not yet implemented
 
> import -> DistillRules where
>     -- Not yet implemented