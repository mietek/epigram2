\section{Using the |Elab| language}
\label{sec:Elaboration.MakeElab}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections, PatternGuards #-}

> module Elaboration.MakeElab where

> import Prelude hiding (exp)

> import Control.Applicative
> import Control.Monad.Error

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.TypeChecker
> import Evidences.TypeCheckRules
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.Edition.ProofState

> import DisplayLang.DisplayTm
> import DisplayLang.PrettyPrint
> import DisplayLang.Name
> import DisplayLang.Scheme

> import Elaboration.ElabProb
> import Elaboration.ElabMonad

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\subsection{Tools for writing elaborators}

The |eCan| instruction asks for the current goal to be solved by the given
elaboration problem when the supplied value is canonical.

> eCan :: VAL -> EProb -> Elab a
> eCan (_ :- _)   prob = eElab (Loc 0) prob
> eCan tt         prob = eElab (Loc 0) (WaitCan (exp tt) prob)

We can type-check a term using the |eCheck| instruction.

> eCheck :: (TY :>: EXP) -> Elab ()
> eCheck (ty :>: tm) = do
>     l <- eAskDevLev
>     chk l (ty :>: (ENil,tm))

The |eCoerce| instruction attempts to coerce a value from the first type to
the second type, either trivially (if the types are definitionally equal) or by
hoping for a proof of the appropriate equation and inserting a coercion.

> eCoerce :: EXP -> EXP -> EXP -> Elab EXP
> eCoerce _S _T s = do
>     eq <- eEqual $ SET :>: (_S, _T)
>     if eq
>         then return s
>         else do
>             q <- eHopeFor $ PRF (EQ SET _S SET _T)
>             return $ (Coeh Coe _S _T q s :$ B0) 

The |eEqual| instruction determines if two types are definitionally equal.

> eEqual :: (TY :>: (EXP, EXP)) -> Elab Bool
> eEqual tyvv = do
>     nsupply <- eAskDevLev
>     return (equal nsupply tyvv)


The |eHope| instruction hopes that the current goal can be solved.

> eHope :: Elab a
> eHope = eElab (Loc 0) ElabHope


The |eHopeFor| instruction hopes for an element of a type.

> eHopeFor :: TY -> Elab EXP
> eHopeFor ty = eCompute (ty :>: eHope)

The |eInfer| instruction infers the type of an evidence term.

> eInfer :: EXP -> Elab EXP
> eInfer tm = do
>     l <- eAskDevLev
>     ty <- inf l (ENil, tm) 
>     return $ PAIR ty tm 


The |eSchedule| instruction asks for the scheduler to deal with other problems
before returning its result.

> eSchedule :: EXP -> Elab a
> eSchedule tm = eElab (Loc 0) (ElabSchedule (ElabDone tm))


\subsection{Elaborating |DInTm|s}

We use the |Elab| language to describe how to elaborate a display term to
produce an evidence term. The |makeElab| and |makeElabInfer| functions read a
display term and use the capabilities of the |Elab| monad to produce a
corresponding evidence term. 

When part of the display syntax needs to be elaborated as a
subproblem, we call |subElab| or |subElabInfer| rather than |makeElab|
or |makeElabInfer| to ensure that elaboration does not take place at
the top level. This means that if the subproblem needs to modify the
proof state (for example, to introduce a $\lambda$) it will create a
new definition to work in. It also ensures that the subproblem can
terminate with the |eElab| instruction, providing a syntactic
representation.

> subElab :: Loc -> (TY :>: DInTmRN) -> Elab EXP
> subElab loc (ty :>: tm) = eCompute (ty :>: makeElab loc tm)

> subElabInfer :: Loc -> DExTmRN -> Elab EXP
> subElabInfer loc tm = eCompute (sigSet :>: makeElabInfer loc tm)

Since we frequently pattern-match on the goal type when elaborating |In| terms,
we abstract it out. Thus |makeElab'| actually implements elaboration.


> makeElab :: Loc -> DInTmRN -> Elab EXP
> makeElab loc tm = makeElab' loc . (:>: tm) . ev =<< eGoal

> makeElab' :: Loc -> (VAL :>: DInTmRN) -> Elab EXP


> -- import <- MakeElabRules
> -- [Feature = Enum] 
> makeElab' loc (PI s t :>: m) | ENUMT e <- ev s , isTuply m = do
>     tm <- subElab loc (wr (def branchesDEF) e t :>: m)
>     x <-  eLambda (fortran "n" [ev t] undefined)
>     return $ (wr (def switchDEF) e (x :$ B0) t tm)
>   where
>     isTuply :: DInTmRN -> Bool
>     isTuply DVOID        = True
>     isTuply (DPAIR _ _)  = True
>     isTuply _            = False

To elaborate a tag with an enumeration as its type, we search for the
tag in the enumeration to determine the appropriate index.

> makeElab' loc (ENUMT t :>: DTAG a) = findTag a (ev t) 0
>   where
>     findTag :: String -> VAL -> Int -> Elab EXP
>     findTag a (CONSE t e) n
>       | TAG b <- ev t , a == b        = return (toNum n)
>       | otherwise                     = findTag a (ev e) (succ n)
>     findTag a _ n  = throwError' . err $ "elaborate: tag `" 
>                                           ++ a 
>                                           ++ " not found in enumeration."
>                       
>     toNum :: Int -> EXP
>     toNum 0  = ZE
>     toNum n  = SU (toNum (n-1))

We elaborate list-like syntax for enumerations into the corresponding inductive
data. This cannot apply in general because it leads to infinite loops when
elaborating illegal values for some descriptions. Perhaps we should remove it
for enumerations as well.

> makeElab' loc (ENUMU :>: DVOID) = 
>     makeElab' loc (ENUMU :>: DNILE)
> makeElab' loc (ENUMU :>: DPAIR s t) =
>     makeElab' loc (ENUMU :>: DCONSE s t)
> -- [/Feature = Enum] 
> -- [Feature = Equality] 
> makeElab' loc (PROP :>: DEq s t) = do
>     s_S <- subElabInfer loc s
>     t_T <- subElabInfer loc t
>     let s :<: _S = extractNeutral s_S
>     let t :<: _T = extractNeutral t_T
>     return $  EQ _S s _T t
> -- [/Feature = Equality] 

> {-
> -- [Feature = IDesc] 
> makeElab' loc (SET :>: DIMU Nothing iI d i) = do
>     iI  :=>: iIv  <- subElab loc (SET :>: iI)
>     d   :=>: dv   <- subElab loc (ARR iIv (idesc $$ A iIv) :>: d)
>     i   :=>: iv   <- subElab loc (iIv :>: i)
>     return $ IMU Nothing iI d i :=>: IMU Nothing iIv dv iv

> makeElab' loc (ty@(IMU _ _ _ _) :>: DTag s xs) =
>     makeElab' loc (ty :>: DCON (DPAIR (DTAG s) (foldr DPAIR DU xs)))
> -- [/Feature = IDesc] 
> -- [Feature = UId] 
> makeElab' loc (UID :>: DTAG s) = return $ TAG s :=>: TAG s
> -- [/Feature = UId] 

> -}

We use underscores |DU| in elaboration to mean "figure this out yourself", while
question marks |DQ| require us to wait for a user-provided value.

> makeElab' loc (ty :>: DU) = eHope
> makeElab' loc (ty :>: DQ s) = eWait s (exp ty)


Elaborating a canonical term with canonical type is a job for |canTy|.

> makeElab' loc ((c :- as)  :>: DC d bs) = do
>     tbs <- canTyM ((c , as) :>: d)
>     bs' <- elabCan (tbs :>: bs)
>     return (d :- bs')
>   where
>    elabCan :: (VAL :>: [ DInTmRN ]) -> Elab [ EXP ]  
>    elabCan (ONE :>: []) = (| [] |)
>    elabCan (SIGMA _S _T :>: (b : bs)) = do 
>      b' <- subElab loc (_S :>: b) 
>      bs' <- elabCan (ev (_T $$. b') :>: bs)
>      return (b' : bs')

There are a few possibilities for elaborating $\lambda$-abstractions. If both the
range and term are constants, then we simply |makeElab| underneath. This avoids
creating some trivial children. 


> makeElab' loc (PI s lkt :>: DL (DK dtm)) | LK t <- ev lkt = do
>     tm <- subElab loc (t :>: dtm)
>     return $ LK tm 


Otherwise, we can simply create a |lambdaParam| in the current development, and
carry on elaborating. We can call |makeElab| here, rather than |subElab|,
because it is a tail call.

> makeElab' loc (ty :>: DL sc) = do
>     ref <- eLambda (dfortran (DL sc))
>     makeElab loc (dScopeTm sc)


We push types in to neutral terms by calling |subElabInfer| on the term, then
coercing the result to the required type. (Note that |eCoerce| will check if the
types are equal, and if so it will not insert a redundant coercion.)

> makeElab' loc (w :>: DN n) = do
>     tt <- subElabInfer loc n
>     let (tm :<: ty) = extractNeutral tt
>     eCoerce ty (exp w) tm



If we already have an evidence term, we just type-check it. This allows
elaboration code to partially elaborate a display term then embed the
resulting evidence term and call the elaborator again.

> makeElab' loc (ty :>: DTIN tm) = eCheck (exp ty :>: tm) >> return tm


If the type is neutral and none of the preceding cases match,
there is nothing we can do but wait for the type to become canonical.
Else fail.

> makeElab' loc (ty :>: tm) = case ty of
>   _ :- _  -> throwError' $ err "makeElab: can't push"
>                            ++ errTyTm (SET :>: exp ty) ++ err "into"
>                            ++ err (renderHouseStyle (pretty tm AppSize)) 
>   _ -> eCan ty (ElabProb tm)

\subsection{Elaborating |DExTm|s}

The |makeElabInfer| command is to |infer| in
subsection~\ref{subsec:Evidences.TypeChecker.type-inference} as |makeElab|
is to |check|. It elaborates the display term and infers its type to
produce a type-term pair in the evidence language.

The result of |makeElabInfer| is of type $\SIGMA{\V{X}}{\Set}{X}$.

> sigSet :: Tm {Body, Exp, n}
> sigSet = SIGMA SET (la "ssv" $ \ x -> x)

> idTM :: String ->   Tm {Body, Exp, n}
> idTM s = la s $ \ x -> x

The |extractNeutral| function separates type-term pairs in both term and value
forms. It avoids clutter in the term representation by splitting it up if it
happens to be a canonical pair, or applying the appropriate eliminators if not.

> extractNeutral :: EXP -> EXP :<: TY
> extractNeutral t = (t $$ Tl) :<: (t $$ Hd) 


Since we use a head-spine representation for display terms, we need to
elaborate the head of an application. The |makeElabInferHead| function
uses the |Elab| monad to produce a type-term pair for the head, and
provides its scheme (if it has one) for argument synthesis. The head
may be a parameter, which is resolved; an embedded evidence term,
which is checked; or a type annotation, which is converted to the
identity function at the given type.

> makeElabInferHead :: Loc -> DHEAD -> Elab (EXP, Maybe Scheme)
> makeElabInferHead loc (DP rn)     = eResolve rn
> makeElabInferHead loc (DTEX tm)   = (| (eInfer tm) , ~Nothing |)
> makeElabInferHead loc (DType ty)  = do
>     tm <- subElab loc (SET :>: ty)
>     return (typeAnnotTM tm, Nothing)
>   where
>     typeAnnotTM :: EXP -> EXP
>     typeAnnotTM tm = PAIR (ARR tm tm) (la "typeAnnot" $ \ x -> x)
> -- [Feature = Equality]
> makeElabInferHead loc (DRefl _T t) = do
>   _T' <- subElab loc (SET :>: _T)
>   t' <- subElab loc (_T' :>: t)
>   (| (PAIR (PRF (EQ _T' t' _T' t')) (Refl _T' t' :$ B0), Nothing) |)
> makeElabInferHead loc (DCoeh coeh _S _T q s) = do
>     _S' <- subElab loc (SET :>: _S)
>     _T' <- subElab loc (SET :>: _T)
>     q' <- subElab loc (PRF (EQ SET _S' SET _T') :>: q)
>     s' <- subElab loc (_S' :>: s)
>     (| (PAIR (eorh coeh _S' _T' q' s') (Coeh coeh _S' _T' q' s' :$ B0), Nothing) |)
>   where
>     eorh :: Coeh -> EXP -> EXP -> EXP -> EXP -> EXP
>     eorh Coe _ _T' _ _ = _T'
>     eorh Coh _S' _T' q' s' = 
>       PRF (EQ _S' s' _T' (Coeh Coe _S' _T' q' s' :$ B0))
> -- [Feature = Equality]


Now we can implement |makeElabInfer|. We use |makeElabInferHead| to elaborate
the head of the neutral term, then call |handleArgs| or |handleSchemeArgs| to
process the spine of eliminators.


> makeElabInfer :: Loc -> DExTmRN -> Elab EXP

> makeElabInfer loc (t ::$ ss) = do
>     (tt, ms) <- makeElabInferHead loc t
>     let (tm :<: ty) = extractNeutral tt
>     case ms of
>         Just sch  -> error "Scheme what scheme?" -- handleSchemeArgs B0 sch  (tm ?? ty :=>: tmv :<: tyv) ss
>         Nothing   -> handleArgs (tm :<: ev ty) ss
>     
>   where

> {-

The |handleSchemeArgs| function takes a list of terms (corresponding to
de Bruijn-indexed variables), the scheme, term and type of the neutral, and a
spine of eliminators in display syntax. It elaborates the eliminators and applies
them to the neutral term, using the scheme to handle insertion of implicit
arguments.

>     handleSchemeArgs :: Bwd (INTM :=>: VAL) -> Scheme INTM ->
>         EXTM :=>: VAL :<: TY -> DSPINE -> Elab (INTM :=>: VAL)

If the scheme is just a type, then we call on the non-scheme |handleArgs|.

>     handleSchemeArgs es (SchType _) ttt as = handleArgs ttt as

If the scheme has an implicit $\Pi$-binding, then we hope for a value of the
relevant type and carry on. Note that we evaluate the type of the binding in the
context |es|.

>     handleSchemeArgs es  (SchImplicitPi (x :<: s) schT)
>                              (tm :=>: tv :<: PI sd t) as = do
>         stm :=>: sv <- eHopeFor (eval s (fmap valueOf es, []))
>         handleSchemeArgs (es :< (stm :=>: sv)) schT
>             (tm :$ A stm :=>: tv $$ A sv :<: t $$ A sv) as

If the scheme has an explicit $\Pi$-binding and we have an argument, then we can
push the expected type into the argument and carry on.
\question{Does this case need to be modified for higher-order schemes?}

>     handleSchemeArgs es  (SchExplicitPi (x :<: schS) schT)
>                              (tm :=>: tv :<: PI sd t) (A a : as) = do
>         let s' = schemeToInTm schS
>         atm :=>: av <- subElab loc (eval s' (fmap valueOf es, []) :>: a)
>         handleSchemeArgs (es :< (atm :=>: av)) schT
>             (tm :$ A atm :=>: tv $$ A av :<: t $$ A av) as

If the scheme has an explicit $\Pi$-binding, but we have no more eliminators,
then we go under the binder and continue processing the scheme in order to
insert any implicit arguments that might be there. We then have to reconstruct
the overall type-term pair from the result.

>     handleSchemeArgs es  (SchExplicitPi (x :<: schS) schT)
>                              (tm :=>: tv :<: PI sd t) [] = do
>         let sv = eval (schemeToInTm schS) (fmap valueOf es, [])
>         tm :=>: tv <- eCompute
>             (PI sv (L $ K sigSetVAL) :>: do
>                 r <- eLambda x
>                 let rt = NP r
>                 handleSchemeArgs (es :< (rt :=>: rt)) schT
>                     (tm :$ A rt :=>: tv $$ A rt :<: t $$ A rt) []
>             )
>         s' :=>: _ <- eQuote sv
>         let  atm  = tm ?? PIV x s' sigSetTM :$ A (NV 0)
>              rtm  = PAIR (PIV x s' (N (atm :$ Fst))) (LAV x (N (atm :$ Snd)))
>         return $ rtm :=>: evTm rtm

Otherwise, we probably have a scheme with an explicit $\Pi$-binding but an
eliminator other than application, so we give up and throw an error. 

>     handleSchemeArgs es sch (_ :=>: v :<: ty) as = throwError' $
>         err "handleSchemeArgs: cannot handle scheme" ++ errScheme sch ++
>         err "with neutral term" ++ errTyVal (v :<: ty) ++
>         err "and eliminators" ++ map ErrorElim as

> -}


The |handleArgs| function is a simplified version of |handleSchemeArgs|, for
neutral terms without schemes. It takes a typed neutral term and a spine of
eliminators in display syntax, and produces a set-value pair in the |Elab| monad.

>     handleArgs :: (EXP :<: VAL) -> DSPINE -> Elab EXP

If we have run out of eliminators, then we just give back the neutral term with
its type.

>     handleArgs (tm :<: ty) [] = do
>         return $ PAIR (exp ty) tm

If we have a term of a labelled type being eliminated with |Call|, we need to
attach the appropriate label to the call and continue with the returned type.

>     handleArgs (tm :<: ty) (A a : as) | 
>            Just (_, _S, _T) <- lambdable ty = do
>         a' <- subElab loc (_S :>: a)  
>         handleArgs (tm $$. a' :<: ev (_T a')) as
>     handleArgs (tm :<: ty) (Hd : as) | Just (_S, _T) <- projable ty =
>         handleArgs (tm $$ Hd :<: ev _S) as
>     handleArgs (tm :<: ty) (Tl : as) | Just (_S, _T) <- projable ty =
>         handleArgs (tm $$ Tl :<: ev (_T (tm $$ Hd))) as

>     -- [Feature = Equality]
>     handleArgs (tm :<: PRF _P) (QA x y q : as) 
>           | EQ _S f _T g <- ev _P
>           , Just (_, _SD, _SC) <- lambdable (ev _S)  
>           , Just (_, _TD, _TC) <- lambdable (ev _T) = do
>       x' <- subElab loc (_SD :>: x)
>       y' <- subElab loc (_TD :>: y)
>       q' <- subElab loc (PRF (EQ _SD x' _TD y') :>: q)
>       handleArgs (tm $$ (QA x' y' q') :<: 
>                    PRF (EQ (_SC x') (f $$. x') (_TC y') (g $$. y'))) as
>
>     handleArgs (tm :<: PRF _P) (Sym : as) | EQ _S s _T t <- ev _P =
>       handleArgs (tm $$ Sym :<: PRF (EQ _T t _S s)) as
>     -- [Feature = Equality]

>     handleArgs (tm :<: ty@(_ :- _)) as =
>         throwError' $ [StrMsg $ "badly typed elimintation in handleArgs? " ++ show tm ,
>                        ErrorTm (Just SET :>: exp ty) ,
>                        StrMsg $ foldr (++) "" (map show as) ]

> {-
>     handleArgs (t :=>: v :<: LABEL l ty) (Call _ : as) = do
>         l' :=>: _ <- eQuote l
>         handleArgs (t :$ Call l' :=>: v $$ Call l :<: ty) as

For all other eliminators, assuming the type is canonical we can use |elimTy|.

>     handleArgs (t :=>: v :<: C cty) (a : as) = do
>         (a', ty') <- elimTy (subElab loc) (v :<: cty) a
>         handleArgs (t :$ fmap termOf a' :=>: v $$ fmap valueOf a' :<: ty') as

> -}

Otherwise, we cannot do anything apart from waiting for the type to become
canonical, so we suspend elaboration and record the current problem.

>     handleArgs (tm :<: ty) as = do
>         eCan ty (ElabInferProb (DTEX tm ::$ as))

