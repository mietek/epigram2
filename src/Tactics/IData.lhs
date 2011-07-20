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
> import Evidences.Primitives
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation
> import ProofState.Interface
> import ProofState.NameResolution

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
>     lev <- getDevLev
>     (x,args,i') <- elabConDesc lev (dtt, aus) (i :$ B0 :<: indty') (ev ty)
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

> elabConDesc :: Int -> (DEF, Bwd (Elim EXP)) -> (EXP :<: TY) -> VAL -> 
>                ProofState (EXP, [(String, Maybe [(String, TY)])], EXP)
> elabConDesc lev d@(dt,_) i@(_ :<: ity) (PI s t) 
>     | not (occurs lev (Just (defName dt)) [] (SET:>:s)) = do
>   makeModule "conarg"
>   aus <- (| paramSpine getInScope |)
>   goIn
>   let sx = fortran "x" [ev t] undefined 
>   x <- assumeParam (sx :<: s)
>   moduleToGoal (def iDescDEF $$. ity)
>   (t',args,i') <- elabConDesc (lev+1) d i (ev t $$. (x :$ B0))
>   dt <- giveOutBelow t'
>   return $ (ISIGMA s (def dt $$$ aus), (sx, Nothing) : args, i')
> elabConDesc lev d@(dt,_) i@(_ :<: ity) (PI s t) = do
>   let xs = fortran "x" [ev t] undefined
>   let t' = t $$. (P (lev,"x",s) :$ B0)
>   case occurs lev Nothing [lev] (SET:>:t') of
>     True -> throwError' $ err "Dep error"
>     False -> do
>       (c,iargs) <- elabInd lev d ity (ev s)
>       (d,args,i') <- elabConDesc lev d i (ev t')
>       return (IPROD (TAG xs) c d, (xs, Just iargs) : args, i')
> elabConDesc _ (dt, das) (i :<: ity) (D d :$ (as :< A i')) | dt == d && matchSpine das as = 
>   return $ (ICONST (PRF (EQ ity i ity i')), [], i')
> elabConDesc _ _ _ x = error $ show x

> matchSpine :: Bwd (Elim EXP) -> Bwd (Elim EXP) -> Bool
> matchSpine B0 B0 = True
> matchSpine (as :< A a) (bs :< A b) 
>   |  P (l,_,_)   :$ B0 <- ev a 
>   ,  P (l',_,_)  :$ B0 <- ev b 
>   ,  l == l' = matchSpine as bs
> matchSpine _ _ = False 

> elabInd :: Int -> (DEF, Bwd (Elim EXP)) -> TY -> VAL -> 
>            ProofState (EXP, [(String, TY)])
> elabInd lev d@(dt,_) ity (PI s t) 
>     | not (occurs lev (Just (defName dt)) [] (SET :>: s)) = do
>   makeModule "indarg"
>   aus <- (| paramSpine getInScope |)
>   goIn
>   let xs = fortran "x" [ev t] undefined 
>   x <- assumeParam (xs :<: s)
>   moduleToGoal (def iDescDEF $$. ity)
>   (t',iargs) <- elabInd (lev+1) d ity (ev t $$. (x :$ B0))
>   dt <- giveOutBelow t'
>   return $ (IPI s (def dt $$$ aus), (xs, s) : iargs) 
> elabInd _ (dt, das) _ (D d :$ (as :< A i')) | dt == d && matchSpine das as = 
>   return $ (IVAR i', [])
> elabInd _ _ _ _ = throwError' $ err "Not SP"

> toSuZe :: Int -> Tm {Body, s, n}
> toSuZe 0 = ZE
> toSuZe n = SU (toSuZe (n-1))

