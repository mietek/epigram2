\section{Elaboration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, TypeOperators, TypeSynonymInstances, GADTs #-}

> module Elaborator where

> import Debug.Trace

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.State
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import BwdFwd
> import Developments
> import Naming
> import PrettyPrint
> import ProofState
> import Root
> import Rooty
> import Rules
> import Tm
> import MissingLibrary

%endif

\subsection{Elaborator}

The |elaborate| command elaborates a term in display syntax, given its type,
to produce an elaborated term and its value representation. It behaves
similarly to |check| from subsection~\ref{subsec:type-checking}, except that
it operates in the |ProofState| monad, so it can create subgoals and
$\lambda$-lift terms.

> elabbedT :: INTM -> ProofState (INTM :=>: VAL)
> elabbedT t = return (t :=>: evTm t)

> elabbedV :: VAL -> ProofState (INTM :=>: VAL)
> elabbedV v = do
>   t <- bquoteHere v
>   return (t :=>: v)

The Boolean parameter indicates whether the elaborator is working at the top
level of the term, because if so, it can create boys in the current development
rather than creating a subgoal.

> elaborate :: Bool -> (TY :>: INDTM) -> ProofState (INTM :=>: VAL)

Here's a case which makes labelled datatypes

> elaborate True (SET :>: MU Nothing d) = do
>     GirlMother (nom := HOLE :<: ty) _ _ <- getMother
>     let fr = nom := FAKE :<: ty
>     xs <- (| boySpine getAuncles |)
>     let lt = N (P fr $:$ xs)
>     let lv = evTm lt
>     (t :=>: v) <- elaborate False (desc :>: d)
>     return (MU (Just lt) t :=>: MU (Just lv) v)

First, some special cases to provide a convenient syntax for writing functions from
interesting types.

> elaborate b (PI UNIT t :>: CON f) = do
>     (m' :=>: m) <- elaborate False (t $$ A VOID :>: f)
>     return $ L (K m') :=>: L (K m)

> elaborate False (y@(PI _ _) :>: t@(C _)) = do
>     y' <- bquoteHere y
>     make ("h" :<: y')
>     goIn
>     elabbedT =<< elabGive t

> elaborate True (PI (MU l d) t :>: CON f) = do
>     (m' :=>: _) <- elaborate False $ case l of
>       Nothing  -> elimOpMethodType $$ A d $$ A t :>: f
>       Just l   -> elimOpLabMethodType $$ A l $$ A d $$ A t :>: f
>     d' <- bquoteHere d
>     (dll :=>: _) <- elaborate False (desc :>: d') -- lambda lift that sucker
>     t' <- bquoteHere t
>     x <- lambdaBoy (fortran t)
>     elabbedT . N $ elimOp :@ [dll, N (P x), t', m']

> elaborate True (PI (SIGMA d r) t :>: CON f) = do
>     let mt =   eval [.a.b.c.
>                  PI (NV a) . L $ fortran r :. [.x.
>                  PI (N (V b :$ A (NV x))) . L $ "" :. [.y.
>                  N (V c :$ A (PAIR (NV x) (NV y)))
>                ]]] $ B0 :< d :< r :< t
>     (m' :=>: m) <- elaborate False (mt :>: f)
>     x <- lambdaBoy (fortran t)
>     elabbedV $ m $$ A (pval x $$ Fst) $$ A (pval x $$ Snd)  -- lambda lift?

> elaborate True (PI (ENUMT e) t :>: m) | isTuply m = do
>     targetsDesc <- withRoot (equal (ARR (ENUMT e) SET :>: (t, L (K desc))))
>     (m' :=>: _) <- elaborate False (branchesOp @@ [e, t] :>: m)
>     e' <- bquoteHere e
>     x  <- lambdaBoy (fortran t)
>     if targetsDesc
>       then elabbedT . N $ switchDOp :@ [e', m', N (P x)]
>       else do
>         t' <- bquoteHere t
>         elabbedT . N $ switchOp :@ [e', N (P x), t', m']
>  where   isTuply :: INDTM -> Bool
>          isTuply VOID = True
>          isTuply (PAIR _ _) = True
>          isTuply _ = False

As some more syntactic sugar, we let inductive types elaborate lists (so |[]| becomes
|@[0]| and |[s / t]| becomes |@ [1 s t]|).

> elaborate b (MU l d :>: VOID) = elaborate b (MU l d :>: CON (PAIR ZE VOID))
> elaborate b (MU l d :>: (PAIR s t)) = elaborate b (MU l d :>: CON (PAIR (SU ZE) (PAIR s t)))

> elaborate b (MONAD d x :>: CON t) = elaborate b (MONAD d x :>: COMPOSITE t)

To elaborate a tag with an enumeration as its type, we search for the tag in the enumeration
to determine the appropriate index.

> elaborate b (ENUMT t :>: TAG a) = findTag a t 0
>   where
>     findTag :: String -> TY -> Int -> ProofState (INTM :=>: VAL)
>     findTag a (CONSE (TAG b) t) n
>       | a == b        = return (toNum n :=>: toNum n)
>       | otherwise     = findTag a t (succ n)
>     findTag a _ n  = throwError' ("elaborate: tag `" ++ a ++ " not found in enumeration.")
>                         
>     toNum :: Int -> Tm {In, p} x
>     toNum 0  = ZE
>     toNum n  = SU (toNum (n-1))

> elaborate b (PRF p :>: VOID) = prove b p

> elaborate b (NU d :>: COIT VOID sty f s) = do
>   d' <- bquoteHere d
>   elaborate b (NU d :>: COIT d' sty f s)

Elaborating a canonical term with canonical type is a job for |canTy|.

> elaborate top (C ty :>: C tm) = do
>     v <- canTy (elaborate False) (ty :>: tm)
>     return $ (C $ fmap (\(x :=>: _) -> x) v) :=>: (C $ fmap (\(_ :=>: x) -> x) v)


If the elaborator encounters a question mark, it simply creates an appropriate subgoal.

> elaborate top (ty :>: Q x) = do
>     ty' <- bquoteHere ty
>     g <- make (x :<: ty')
>     return (g :=>: evTm g)


There are a few possibilities for elaborating $\lambda$-abstractions. If both the
range and term are constants, and we are not at top level, then we simply elaborate
underneath. This avoids creating some trivial children. It means that elaboration
will not produce a fully $\lambda$-lifted result, but luckily the compiler can deal
with constant functions.

> elaborate False (PI s (L (K t)) :>: L (K dtm)) = do
>     (tm :=>: tmv) <- elaborate False (t :>: dtm)
>     return (L (K tm) :=>: L (K tmv))

If we are not at top level, we create a subgoal corresponding to the term, solve it
by elaboration, then return the reference. 

> elaborate False (ty :>: L sc) = do
>     Just _ <- return $ lambdable ty
>     pi' <- bquoteHere ty
>     make ("h" :<: pi')
>     goIn
>     l <- lambdaBoy (fortran (L sc))
>     h <- elabGive (underScope sc l)
>     return (h :=>: evTm h)

If we are at top level, we can simply create a |lambdaBoy| in the current development,
and carry on elaborating.

> elaborate True (ty :>: L sc) = do
>     Just _ <- return $ lambdable ty
>     l <- lambdaBoy (fortran (L sc))
>     _ :=>: ty <- getGoal "elaborate lambda"
>     elaborate True (ty :>: underScope sc l)
>     
    
Much as with type-checking, we push types in to neutral terms by calling |elabInfer| on
the term, then checking the inferred type is what we pushed in.

> elaborate top (w :>: N n) = do
>   (y :>: n) <- elabInfer n
>   eq <- withRoot (equal (SET :>: (w, y)))
>   guard eq `replaceError` ("elaborate: inferred type " ++ show y ++ " of " ++ show n
>                              ++ " is not " ++ show w)
>   return (N n :=>: evTm (N n))


If nothing else matches, give up and report an error.

> elaborate top tt = throwError' ("elaborate: can't cope with " ++ show tt)


The |elabInfer| command is to |infer| in subsection~\ref{subsec:type-inference} 
as |elaborate| is to |check|. It infers the type of a display term, calling on
the elaborator rather than the type-checker. Most of the cases are similar to
those of |infer|.

> elabInfer :: EXDTM -> ProofState (TY :>: EXTM)

> elabInfer (P x) = return (pty x :>: P x)

> elabInfer (t :$ s) = do
>     (C ty :>: t') <- elabInfer t
>     (s', ty') <- elimTy (elaborate False) (evTm t' :<: ty) s
>     let s'' = fmap (\(x :=>: _) -> x) s'
>     return (ty' :>: (t' :$ s''))

> elabInfer (op :@ ts) = do
>   (vs, t) <- opTy op (elaborate False) ts
>   let vs' = fmap (\(x :=>: _) -> x) vs
>   return (t :>: op :@ vs')

> elabInfer (t :? ty) = do
>   (ty' :=>: vty)  <- elaborate False (SET :>: ty)
>   (t'  :=>: _)    <- elaborate False (vty :>: t)
>   return (vty :>: t' :? ty')

> elabInfer tt = throwError' ("elabInfer: can't cope with " ++ show tt)


\subsubsection{Proof Construction}

This operation, part of elaboration, tries to prove a proposition, leaving the
hard bits for the human.

> prove :: Bool -> VAL -> ProofState (INTM :=>: VAL)
> prove b TRIVIAL = return (VOID :=>: VOID)
> prove b (AND p q) = do
>   (pt :=>: pv) <- prove False p
>   (qt :=>: qv) <- prove False q
>   return (PAIR pt qt :=>: PAIR pv qv)
> prove b p@(ALL _ _) = elaborate b (PRF p :>: L ("__prove" :. VOID))
> prove b p@(EQBLUE (y0 :>: t0) (y1 :>: t1)) = useRefl <|> unroll <|> search p where
>   useRefl = do
>     guard =<< withRoot (equal (SET :>: (y0, y1)))
>     guard =<< withRoot (equal (y0 :>: (t0, t1)))
>     let w = pval refl $$ A y0 $$ A t0
>     qw <- bquoteHere w
>     return (qw :=>: w)
>   unroll = do
>     Right p <- return $ opRun eqGreen [y0, t0, y1, t1]
>     (t :=>: v) <- prove False p
>     return (CON t :=>: CON v)
> prove b p@(N (qop :@ [y0, t0, y1, t1])) | qop == eqGreen = do
>   let g = EQBLUE (y0 :>: t0) (y1 :>: t1)
>   (_ :=>: v) <- prove False g
>   let v' = v $$ Out
>   t' <- bquoteHere v'
>   return (t' :=>: v')
> prove b p = search p

> search :: VAL -> ProofState (INTM :=>: VAL)
> search p = do
>   es <- getAuncles
>   aunclesProof es p <|> elaborate False (PRF p :>: Q "")

> aunclesProof :: Entries -> VAL -> ProofState (INTM :=>: VAL)
> aunclesProof B0 p = empty
> aunclesProof (es :< E ref _ (Boy _) _) p =
>   synthProof (pval ref :<: pty ref) p <|> aunclesProof es p
> aunclesProof (es :< _) p = aunclesProof es p  -- for the time being

> synthProof :: (VAL :<: TY) -> VAL -> ProofState (INTM :=>: VAL)
> synthProof (v :<: PRF p) p' = do
>   guard =<< withRoot (equal (PROP :>: (p, p')))
>   t <- bquoteHere v
>   return (t :=>: v)
> synthProof _ _ = (|)



\subsection{Display-Term Commands}

\subsubsection{Information}

The |infoElaborate| command calls |elabInfer| on the given neutral display term,
evaluates the resulting term, bquotes it and returns a pretty-printed string
representation. Note that it works in its own module which it discards at the
end, so it will not leave any subgoals lying around in the proof state.

> infoElaborate :: INDTM -> ProofState String
> infoElaborate (N tm) = do
>     makeModule "elab"
>     goIn
>     _ :>: tm' <- elabInfer tm
>     tm <- bquoteHere (evTm (N tm'))
>     s <- prettyHere tm
>     goOut
>     dropModule
>     return s
> infoElaborate _ = throwError' "infoElaborate: can only elaborate neutral terms."

The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: INDTM -> ProofState String
> infoInfer (N tm) = do
>     makeModule "infer"
>     goIn
>     ty :>: _ <- elabInfer tm
>     ty' <- bquoteHere ty
>     s <- prettyHere ty'
>     goOut
>     dropModule
>     return s
> infoInfer _ = throwError' "infoInfer: can only infer the type of neutral terms."


\subsubsection{Construction}

The |elabGive| command elaborates the given display term in the appropriate type for
the current goal, and calls the |give| command on the resulting term. If its argument
is a nameless question mark, it avoids creating a pointless subgoal by simply returning
a reference to the current goal (applied to the appropriate shared parameters).

> elabGive :: INDTM -> ProofState INTM
> elabGive tm = elabGive' tm <* goOut

> elabGiveNext :: INDTM -> ProofState INTM
> elabGiveNext tm = elabGive' tm <* (nextGoal <|> goOut)

> elabGive' :: INDTM -> ProofState INTM
> elabGive' tm = do
>     tip <- getDevTip
>     case tip of         
>         Unknown (tipTyTm :=>: tipTy) -> do
>             case tm of
>                 Q "" -> do
>                     GirlMother ref _ _ <- getMother
>                     aus <- getGreatAuncles
>                     return (N (P ref $:$ aunclesToElims (aus <>> F0)))
>                 _ -> do
>                     (tm' :=>: tv) <- elaborate True (tipTy :>: tm)
>                     give' tm'
>         _  -> throwError' "elabGive: only possible for incomplete goals."


The |elabMake| command elaborates the given display term in a module to produce a type,
then converts the module to a goal with that type. Thus any subgoals produced by 
elaboration will be children of the resulting goal.

> elabMake :: (String :<: INDTM) -> ProofState INTM
> elabMake (s :<: ty) = do
>     makeModule s
>     goIn
>     tt <- elaborate False (SET :>: ty)
>     tm <- moduleToGoal tt
>     goOut
>     return tm


The |elabPiBoy| command elaborates the given display term to produce a type, and
creates a $\Pi$-boy with that type.

> elabPiBoy :: (String :<: INDTM) -> ProofState ()
> elabPiBoy (s :<: ty) = do
>     tt <- elaborate True (SET :>: ty)
>     piBoy' (s :<: tt)
>     return ()


\subsection{$\lambda$-lifting}

The |gimme| operator elaborates every definition in the proof state, thereby
ensuring it is fully $\lambda$-lifted. Starting from the root of the proof
state, it processes each node in turn, first processing any children, then
the node itself.

> gimme :: ProofState ()
> gimme = much goOut >> processNode
>   where
>     processNode :: ProofState ()
>     processNode = do
>         optional (do
>             goIn
>             much goUp
>             processNode
>             much (goDown >> processNode)
>             goOut
>           )
>         regive
>
>     regive :: ProofState ()
>     regive = do
>         tip <- getDevTip
>         m <- getMother
>         case {- |trace ("regive " ++ show (motherName m)) $| -} tip of
>             Defined tm (tipTyTm :=>: tipTy) -> do
>                 putDevTip (Unknown (tipTyTm :=>: tipTy))
>                 (tm' :=>: tv) <- elaborate True (tipTy :>: tm)
>                 Unknown tt <- getDevTip
>                 putDevTip (Defined tm' tt)
>             _ -> return ()
