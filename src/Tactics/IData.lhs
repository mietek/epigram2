\section{Datatype declaration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternGuards #-}

> module Tactics.IData where

> import Control.Applicative
> import Control.Monad.Identity
> import Control.Monad.Error

> import Data.Monoid hiding (All)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.NatFinVec
> import Kit.BwdFwd

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Module
> import ProofState.Interface.Lifting
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import ProofState.Interface.Solving
> import ProofState.Interface.Search
> import ProofState.Interface.NameResolution

> import Elaboration.Elaborator

> import Tactics.Unification

> import DisplayLang.Name
> import DisplayLang.DisplayTm

> import Debug.Trace

%endif

> unP :: Tm {Head, Exp, Z} -> (Int, String, TY)
> unP (P l) = l

> ielabData :: String -> [ (String , DInTmRN) ] -> DInTmRN ->
>                        [ (String , DInTmRN) ] -> ProofState EXP
> ielabData nom pars indty scs = do
>   oldaus <- (| paramSpine getInScope |)
>   makeModule nom
>   goIn
>   tnom <- makeModule nom
>   goIn
>   pars' <- traverse (\(x,y) -> do  
>     make ((x ++ "Ty") :<: SET)
>     goIn
>     y' <- elabGive y
>     r <- assumeParam (x :<: y')
>     return (x,y')) pars
>   make ("iTy" :<: SET)
>   goIn
>   indty' <- elabGive indty
>   (dtt, tt) <- moduleToGoal' (ARR indty' SET)
>   goOut
>   pars'' <- traverse (\(p,pty) -> assumeParam (p :<: pty)) pars'
>   let aus = oldaus <+> bwdList (map (\x -> A (x :$ B0)) pars'')
>   moduleToGoal (ARR indty' SET)
>   dt <- give tt
>   ctys <- traverse (\(s,cty) -> do
>     cnom <- makeModule s
>     goIn
>     make ((s ++ "Ty") :<: SET)
>     goIn
>     cty' <- elabGive cty
>     moduleToGoal cty'
>     goOut
>     return (s, cnom, cty') 
>     ) scs
>   goTo tnom
>   cDs <- traverse (\(s,cnom,ty) -> do
>     make (s ++ "D" :<: ARR indty' (def iDescDEF $$. indty'))
>     goIn 
>     i <- lambdaParam "i"
>     (x,args,i') <- elabConDesc (dtt, aus) (i :$ B0 :<: indty') (ev ty)
>     d <- giveOutBelow x
>     return (cnom,d,args,i')
>     ) ctys
>   make ("conNames" :<: ENUMU)
>   goIn
>   dcns <- giveOutBelow (foldr (\(s,_,_) e -> CONSE (TAG s) e) NILE ctys) 
>   let cns = def dcns $$$ aus
>   make ("conDescs" :<: ARR indty' (def branchesDEF $$. cns
>                                     $$. (LK (def iDescDEF $$. indty'))))
>   goIn 
>   ii <- lambdaParam "i"
>   dcds <- giveOutBelow (foldr (\(_,dd,_,_) dds -> 
>                                   PAIR (def dd $$$ aus $$. (ii :$ B0)) dds)
>                               ZERO cDs)
>   let cds = def dcds $$$ aus
>   ii <- lambdaParam "i"
>   giveOutBelow $ IMU indty' (la "i'" $ \i' -> IFSIGMA (wr cns) (wr cds i')) (ii :$ B0)
>   traverse (\(e,(cnom,d,args,i')) -> do
>     goTo cnom
>     hs <- traverse lambdaParam (map fst args)
>     give $ CON (PAIR (toSuZe e) 
>                  (foldr (\x y -> PAIR (x :$ B0) y) (Refl indty' i' :$ B0) hs))
>     goOut
>     ) (zip [0..] cDs)
>   goOut
>   return $ def dt $$$ oldaus

> elabConDesc :: (DEF, Bwd (Elim EXP)) -> (EXP :<: TY) -> VAL -> 
>                ProofState (EXP, [(String, Maybe [(String, TY)])], EXP)
> elabConDesc d@(dt,_) i@(_ :<: ity) (PI s t) 
>     | not (occurs (Just (defName dt)) [] [] s) = do
>   makeModule "conarg"
>   aus <- (| paramSpine getInScope |)
>   goIn
>   let sx = fortran "x" [ev t] undefined 
>   x <- assumeParam (sx :<: s)
>   moduleToGoal (def iDescDEF $$. ity)
>   (t',args,i') <- elabConDesc d i (ev t $$. (x :$ B0))
>   dt <- giveOutBelow t'
>   return $ (ISIGMA s (def dt $$$ aus), (sx, Nothing) : args, i')
> elabConDesc d@(dt,_) i@(_ :<: ity) (PI s t) = do
>   lev <- getDevLev
>   let xs = fortran "x" [ev t] undefined
>   let t' = ev t $$. (P (lev,"x",s) :$ B0)
>   case occurs Nothing [lev] [] t' of
>     True -> throwError' $ err "Dep error"
>     False -> do
>       (c,iargs) <- elabInd d ity (ev s)
>       (d,args,i') <- elabConDesc d i t'
>       return (IPROD (TAG xs) c d, (xs, Just iargs) : args, i')
> elabConDesc (dt, das) (i :<: ity) (D d _ Hole :$ (as :< A i')) | dt == d && matchSpine das as = 
>   return $ (ICONST (PRF (EQ ity i ity i')), [], i')

> matchSpine :: Bwd (Elim EXP) -> Bwd (Elim EXP) -> Bool
> matchSpine B0 B0 = True
> matchSpine (as :< A a) (bs :< A b) 
>   |  P (l,_,_)   :$ B0 <- ev a 
>   ,  P (l',_,_)  :$ B0 <- ev b 
>   ,  l == l' = matchSpine as bs
> matchSpine _ _ = False 

> elabInd :: (DEF, Bwd (Elim EXP)) -> TY -> VAL -> 
>            ProofState (EXP, [(String, TY)])
> elabInd d@(dt,_) ity (PI s t) 
>     | not (occurs (Just (defName dt)) [] [] s) = do
>   makeModule "indarg"
>   aus <- (| paramSpine getInScope |)
>   goIn
>   let xs = fortran "x" [ev t] undefined 
>   x <- assumeParam (xs :<: s)
>   moduleToGoal (def iDescDEF $$. ity)
>   (t',iargs) <- elabInd d ity (ev t $$. (x :$ B0))
>   dt <- giveOutBelow t'
>   return $ (IPI s (def dt $$$ aus), (xs, s) : iargs) 
> elabInd (dt, das) _ (D d _ Hole :$ (as :< A i')) | dt == d && matchSpine das as = 
>   return $ (IVAR i', [])
> elabInd _ _ _ = throwError' $ err "Not SP"

> toSuZe :: Int -> Tm {Body, s, n}
> toSuZe 0 = ZE
> toSuZe n = SU (toSuZe (n-1))

> {-
>   make ("ConNames" :<: NP enumREF) 
>   goIn
>   (e :=>: ev) <- giveOutBelow (foldr (\(t,_) e -> CONSE (TAG t) e) NILE scs)
>   make ("ConDescs" :<: 
>           ARR (N indtye) (N (branchesOp 
>                               :@ [ N e
>                                  , L $ K (N (P idescREF :$ A (N indtye)))
>                                  ])))
>   goIn
>   i <- lambdaParam "i"
>   (cs' :=>: _) <- giveOutBelow (foldr PAIR VOID (map (\(_,_,c,_) -> N (c :$ A (NP i))) cs))

>   make ("DataTy" :<: ARR (N indtye) SET)
>   goIn
>   i <- lambdaParam "i"
>   let d = L $ "i" :.IFSIGMA (N e) (N (cs' :$ A (NV 0)))
>       (allowingTy, allowedBy)  =  imkAllowed ("i", indtye, NV 0) pars' 
>                         -- \pierre{XXX: NV 0 refers to the .i. in the giveOut}
>       label                    =  ANCHOR (TAG nom) allowingTy allowedBy
>   (dty :=>: dtyv) <- giveOutBelow (IMU (Just (L $ "i" :. [.i. label])) (N indtye) d (NP i))

We specialise the induction operator to this datatype, ensuring the label is
assigned throughout, so the label will be preserved when eliminating by induction.

This code attempts to find out if the definitions from tests/TaggedInduction
are in scope, if so you get nicer induction principles (:

>   (do (icase,_,_) <- resolveHere [("TData",Rel 0),("tcase",Rel 0)]
>       makeModule "Case"
>       goIn
>       i <- assumeParam ("i" :<: (N indtye :=>: indtyv))
>       v <- assumeParam (comprefold (concat (map (\(_,_,_,c) -> c) cs)) 
>                         :<: (N (dty :$ A (NP i)) :=>: dtyv $$ A (NP i)))
>       let caseTm = P icase :$ A (N indtye) 
>                            :$ A (PAIR (N e) (PAIR (N cs') VOID))
>                            :$ A (NP i) :$ A (NP v)
>       caseV :<: caseTy <- inferHere caseTm
>       caseTy' <- bquoteHere caseTy
>       moduleToGoal (isetLabel (L $ "i" :. [.i. label]) caseTy')
>       giveOutBelow (N caseTm)
>       return ()) `catchError` \_ -> return ()

>   (do (dind,_,_) <- resolveHere [("TData",Rel 0),("tind",Rel 0)]
>       makeModule "Ind"
>       goIn
>       i <- assumeParam ("i" :<: (N indtye :=>: indtyv))
>       v <- assumeParam (comprefold (concat (map (\(_,_,_,c) -> c) cs)) 
>                         :<: (N (dty :$ A (NP i)) :=>: dtyv $$ A (NP i)))
>       let dindT = P dind :$ A (N indtye) 
>                          :$ A (PAIR (N e) (PAIR (N cs') VOID))
>                          :$ A (NP i) :$ A (NP v)
>       dindV :<: dindTy <- inferHere dindT
>       dindTy' <- bquoteHere dindTy
>       moduleToGoal (isetLabel (L $ "i" :. [.i. label]) dindTy')
>       giveOutBelow (N dindT)
>       return ()) `catchError` \_ -> 
>     (do let indTm = P (lookupOpRef iinductionOp) :$ A (N indtye) :$ A d
>         indV :<: indTy <- inferHere indTm
>         indTy' <- bquoteHere indTy
>         make ("Ind" :<: isetLabel (L $ "i" :. [.i. label]) indTy')
>         goIn
>         giveOutBelow (N indTm)
>         return ())
>   giveOutBelow $ N dty


This is a hack, and should probably be replaced with a version that tests for
equality, so it doesn't catch the wrong |MU|s.

\pierre{The match on the |dataTy| anchor is yet another disgusting
hack. When loading the @TaggedInduction.pig@ file, you are able to get
much nicer induction principles. However, the resulting induction
principle will target |dataTy| instead of the current
|nom|. Therefore, we hack the hack so that it hacks when you hack. Yo,
dawg.}

> isetLabel :: INTM -> INTM -> INTM
> isetLabel l (IMU Nothing ity tm i) = IMU (Just l) ity tm i
> isetLabel l (IMU (Just (LK (ANCHOR (TAG x) _ _))) ity tm i) 
>               | x == "dataTy" = IMU (Just l) ity tm i
> isetLabel l (L (x :. t)) = L (x :. isetLabel l t)
> isetLabel l (L (K t)) = L (K (isetLabel l t))
> isetLabel l (C c) = C (fmap (isetLabel l) c)
> isetLabel l (N n) = N (isetLabelN l n)

> isetLabelN :: INTM -> EXTM -> EXTM
> isetLabelN l (P x) = P x
> isetLabelN l (V n) = V n
> isetLabelN l (op :@ as) = op :@ map (isetLabel l) as
> isetLabelN l (f :$ a) = isetLabelN l f :$ fmap (isetLabel l) a
> isetLabelN l (t :? ty) = isetLabel l t :? isetLabel l ty


> import -> CochonTactics where

> occursM :: REF -> Mangle (Ko Any) REF REF
> occursM r = Mang
>             {  mangP = \ x _ -> Ko (Any (r == x))
>             ,  mangV = \ _ _ -> Ko (Any False)
>             ,  mangB = \ _ -> occursM r
>             }

> swapM :: REF -> REF -> Mangle Identity REF REF
> swapM r s = Mang
>             {  mangP = \ x xes ->
>                          if x == r then (| ((P s) $:$) xes |)
>                                    else (| ((P x) $:$) xes |)
>             ,  mangV = \ i ies -> (|(V i $:$) ies|)
>             ,  mangB = \ _ -> swapM r s
>             }

> capM :: REF -> Int -> Mangle Identity REF REF
> capM r i = Mang
>             {  mangP = \ x xes ->
>                          if x == r then (| ((V i) $:$) xes |)
>                                    else (| ((P x) $:$) xes |)
>             ,  mangV = \ j jes -> (|(V j $:$) jes|)
>             ,  mangB = \ _ -> capM r (i+1)
>             }

> occurs :: REF -> INTM -> Bool
> occurs r i = getAny (unKo (occursM r % i))

> uncur 1 v t = N (v :$ A (N t))
> uncur i v t = uncur (i-1) (v :$ A (N (t :$ Fst))) (t :$ Snd)

> compre :: Eq a => [a] -> [a] -> [a] 
> compre [] _ = [] 
> compre _ [] = [] 
> compre (a : as) (b : bs) | a == b = a : compre as bs 
> compre (a : as) (b : bs) = [] 
 
> comprefold :: Eq a => [[a]] -> [a] 
> comprefold [] = [] 
> comprefold (as : ass) = foldr compre as ass 
> -}
