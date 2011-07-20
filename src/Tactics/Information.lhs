\section{Presenting Information}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Tactics.Information where

> import Control.Applicative hiding (empty)
> import Control.Monad.State
> import Text.PrettyPrint.HughesPJ

> import Evidences.Tm hiding (($$))
> import Evidences.NameSupply

> import ProofState.Structure

> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation

> import ProofState.Interface
> import ProofState.NameResolution

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer
> import DisplayLang.PrettyPrint

> import Elaboration.ElabProb
> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.RunElab
> import Elaboration.Scheduler
> import Elaboration.Elaborator

> import Distillation.Distiller
> import Distillation.Scheme

> import Kit.BwdFwd

%endif


> infoInScope :: ProofState String
> infoInScope = do
>     pc <- get
>     inScope <- getInScope
>     return (showEntriesAbs inScope)

> infoDump :: ProofState String
> infoDump = gets show



The |infoElaborate| command calls |elabInfer| on the given neutral display term,
evaluates the resulting term and returns a pretty-printed string
representation. Note that it works in its own module which it discards at the
end, so it will not leave any subgoals lying around in the proof state.

> infoElaborate :: DExTmRN -> ProofState String
> infoElaborate tm = draftModule "__infoElaborate" (do
>     (tm' :<: ty) <- elabInfer' tm
>     s <- prettyPS (ty :>: tm')
>     return (renderHouseStyle s)
>  )


The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: DExTmRN -> ProofState String
> infoInfer tm = draftModule "__infoInfer" (do
>     (_ :<: ty) <- elabInfer' tm
>     s <- prettyPS (SET :>: ty)
>     return (renderHouseStyle s)
>  )



The |infoContextual| command displays a distilled list of things in
the context, parameters if the argument is False or definitions if the
argument is True.

> infoHypotheses  = infoContextual False
> infoContext     = infoContextual True

> infoContextual :: Bool -> ProofState String
> infoContextual gals = do
>     inScope <- getInScope
>     bsc <- gets inBScope
>     d <- help bsc inScope
>     return (renderHouseStyle d)
>   where
>     help :: BScopeContext -> Entries -> ProofState Doc
>     help bsc B0 = return empty
>     help bsc (es :< EParam k s ty _) | not gals = do
>         docTy  <- prettyPSAt (pred ArrSize) (SET :>: ty)
>         d      <- help bsc es
>         return $ d $$ prettyBKind k (text s <+> kword KwAsc <+> docTy)


<     help bsc (es :< EDEF ref _ _ _ _ _) | gals = do
<         ty     <- bquoteHere $ removeShared (paramSpine es) (pty ref)
<         docTy  <- prettyPS (SET :>: ty)
<         d      <- help bsc es
<         return $ d $$ (text (showRelName (christenREF bsc ref))
<                                 <+> kword KwAsc <+> docTy)


>     help bsc (es :< _) = help bsc es



<     removeShared :: Spine {TT} REF -> TY -> TY
<     removeShared []       ty        = ty
<     removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)


This old implementation is written using a horrible imperative hack that saves
the state, throws away bits of the context to produce an answer, then restores
the saved state. We can get rid of it once we are confident that the new version
(above) produces suitable output.

< infoContextual' :: Bool -> ProofState String
< infoContextual' gals = do
<     save <- get
<     let bsc = inBScope save
<     me <- getCurrentName
<     ds <- many (hypsHere bsc me <* optional killBelow <* goOut <* removeEntryAbove)
<     d <- hypsHere bsc me
<     put save
<     return (renderHouseStyle (vcat (d:reverse ds)))
<  where
<    hypsHere :: BScopeContext -> Name -> ProofState Doc
<    hypsHere bsc me = do
<        es <- getEntriesAbove
<        d <- hyps bsc me
<        putEntriesAbove es
<        return d
<    
<    killBelow = do
<        l <- getLayer
<        replaceLayer (l { belowEntries = NF F0 })
<
<    hyps :: BScopeContext -> Name -> ProofState Doc
<    hyps bsc me = do
<        es <- getEntriesAbove
<        case (gals, es) of
<            (_, B0) -> return empty
<            (False, es' :< EPARAM ref _ k _ _) -> do
<                putEntriesAbove es'
<                ty' <- bquoteHere (pty ref)
<                docTy <- prettyPS (SET :>: ty')
<                d <- hyps bsc me
<                return (d $$ prettyBKind k (text (showRelName (christenREF bsc ref)) <+> kword KwAsc <+> docTy))
<            (True, es' :< EDEF ref _ _ _ _ _) -> do
<                goIn
<                es <- getEntriesAbove
<                (ty :=>: _) <- getGoal "hyps"
<                ty' <- bquoteHere (evTm (inferGoalType es ty))
<                docTy <- prettyPS (SET :>: ty')
<                goOut
<                putEntriesAbove es'
<                d <- hyps bsc me
<                return (d $$ (text (showRelName (christenREF bsc ref)) <+> kword KwAsc <+> docTy))
<            (_, es' :< _) -> putEntriesAbove es' >> hyps bsc me



> infoScheme :: RelName -> ProofState String
> infoScheme x = do
>     (_, l, ms) <- resolveHere x
>     case ms of
>         Just sch -> do
>             d <- prettySchemePS (stripScheme l sch)
>             return (renderHouseStyle d)
>         Nothing -> return (showRelName x ++ " does not have a scheme.")



The |infoWhatIs| command displays a term in various representations.

> infoWhatIs :: DExTmRN -> ProofState String
> infoWhatIs tmd = draftModule "__infoWhatIs" (do
>     (tm :<: ty) <- elabInfer' tmd
>     tms <- distillPS (ty :>: tm)
>     tys <- distillPS (SET :>: ty)
>     return (unlines
>         [  "Parsed term:", show tmd
>         ,  "Elaborated term:", show tm
>         ,  "Distilled term:", show tms
>         ,  "Pretty-printed term:", renderHouseStyle (pretty tms maxBound)
>         ,  "Inferred type:", show ty
>         ,   "Distilled type:", show tys
>         ,   "Pretty-printed type:", renderHouseStyle (pretty tys maxBound)
>         ])
>   )


The |prettyProofState| command generates a pretty-printed representation
of the proof state at the current location.

> prettyProofState :: ProofState String
> prettyProofState = do
>     inScope <- getInScope
>     me <- getCurrentName
>     d <- prettyES inScope me
>     return (renderHouseStyle d)
>
> prettyES :: Entries -> Name -> ProofState Doc
> prettyES aus me = do
>         es <- replaceEntriesAbove B0
>         cs <- putBelowCursor F0
>         case (es, cs) of
>             (B0, F0)  -> prettyEmptyTip
>             _   -> do
>                 d <- prettyEs empty (es <>> F0)
>                 d' <- case cs of
>                     F0  -> return d
>                     _   -> do
>                         d'' <- prettyEs empty cs
>                         return (d $$ text "---" $$ d'')
>                 tip <- prettyTip
>                 putEntriesAbove es
>                 putBelowCursor cs
>                 return (lbrack <+> d' $$ rbrack <+> tip)
>  where
>     prettyEs :: Doc -> Fwd (Entry Bwd) -> ProofState Doc
>     prettyEs d F0         = return d
>     prettyEs d (e :> es) = do
>         putEntryAbove e
>         ed <- prettyE e
>         prettyEs (d $$ ed) es
>
>     prettyE (EParam k x ty l)  = do
>         tyd <- distillPS (SET :>: ty)
>         return (prettyBKind k
>                  (text x  <+> kword KwAsc
>                           <+> pretty tyd (pred ArrSize)))
>      
>     prettyE (EDef def _ _) = do
>         goIn
>         d <- prettyES aus me
>         goOut
>         return (sep  [  text (fst (last (defName def))) 
>                      ,  nest 2 d <+> kword KwSemi
>                      ])

>     prettyE (EModule n _) = do
>         goIn
>         d <- prettyES aus me
>         goOut
>         return (sep  [  text (fst (last n)) 
>                      ,  nest 2 d <+> kword KwSemi
>                      ])
>
>     prettyEmptyTip :: ProofState Doc
>     prettyEmptyTip = do
>         tip <- getDevTip
>         case tip of
>             Module -> return (brackets empty)
>             _ -> do
>                 tip <- prettyTip
>                 return (kword KwDefn <+> tip)

>     prettyTip :: ProofState Doc
>     prettyTip = do
>         tip <- getDevTip
>         case tip of
>             Module -> return empty
>             Unknown ty hk -> do
>                 tyd <- distillPS (SET :>: ty)
>                 return (prettyHKind hk <+> kword KwAsc <+> pretty tyd maxBound)

>             Suspended ty prob hk -> do
>                 tyd <- prettyPS (SET :>: ty)
>                 return (text ("(SUSPENDED: " ++ show prob ++ ")")
>                             <+> prettyHKind hk <+> kword KwAsc <+> tyd)

>             Defined (ty :>: tm) -> do
>                 tyd <- distillPS (SET :>: ty)
>                 tmd <- distillPS (ty :>: tm)
>                 return (pretty tmd (pred ArrSize) <+> kword KwAsc
>                             <+> pretty tyd maxBound)

>     prettyHKind :: HKind -> Doc
>     prettyHKind Waiting    = text "?"
>     prettyHKind Hoping     = text "HOPING?"
>     prettyHKind (Crying s) = text $ "(CRYING: " ++ s ++ ")"


The |elm| Cochon tactic elaborates a term, then starts the scheduler to
stabilise the proof state, and returns a pretty-printed representation of the
final type-term pair (using a quick hack).

> elmCT :: DExTmRN -> ProofState String
> elmCT tm = do
>     suspend ("elab" :<: sigSet) (ElabInferProb tm) Hoping
>     startScheduler
>     infoElaborate (DP [("elab", Rel 0)] ::$ [])


