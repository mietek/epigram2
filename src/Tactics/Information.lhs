\section{Presenting Information}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Tactics.Information where

> import Control.Applicative hiding (empty)
> import Control.Monad.State
> import Text.PrettyPrint.HughesPJ

> import NameSupply.NameSupply

> import Evidences.Eval hiding (($$))
> import qualified Evidences.Eval (($$))
> import Evidences.Tm

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import ProofState.Edition.ProofContext
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Lifting
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Module
> import ProofState.Interface.NameResolution

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
>     return (showEntries (inBScope pc) inScope)

> infoDump :: ProofState String
> infoDump = gets show


The |infoElaborate| command calls |elabInfer| on the given neutral display term,
evaluates the resulting term, bquotes it and returns a pretty-printed string
representation. Note that it works in its own module which it discards at the
end, so it will not leave any subgoals lying around in the proof state.

> infoElaborate :: DExTmRN -> ProofState String
> infoElaborate tm = draftModule "__infoElaborate" (do
>     (tm' :=>: tmv :<: ty) <- elabInfer' tm
>     tm'' <- bquoteHere tmv
>     s <- prettyHere (ty :>: tm'')
>     return (renderHouseStyle s)
>  )


The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: DExTmRN -> ProofState String
> infoInfer tm = draftModule "__infoInfer" (do
>     (_ :<: ty) <- elabInfer' tm
>     ty' <- bquoteHere ty
>     s <- prettyHere (SET :>: ty')
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
>     help bsc (es :< EPARAM ref _ k _ _) | not gals = do
>         ty     <- bquoteHere (pty ref)
>         docTy  <- prettyHereAt (pred ArrSize) (SET :>: ty)
>         d      <- help bsc es
>         return $ d $$ prettyBKind k (text (showRelName (christenREF bsc ref))
>                                               <+> kword KwAsc <+> docTy)
>     help bsc (es :< EDEF ref _ _ _ _ _) | gals = do
>         ty     <- bquoteHere $ removeShared (paramSpine es) (pty ref)
>         docTy  <- prettyHere (SET :>: ty)
>         d      <- help bsc es
>         return $ d $$ (text (showRelName (christenREF bsc ref))
>                                 <+> kword KwAsc <+> docTy)
>     help bsc (es :< _) = help bsc es

>     removeShared :: Spine {TT} REF -> TY -> TY
>     removeShared []       ty        = ty
>     removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)


This old implementation is written using a horrible imperative hack that saves
the state, throws away bits of the context to produce an answer, then restores
the saved state. We can get rid of it once we are confident that the new version
(above) produces suitable output.

> infoContextual' :: Bool -> ProofState String
> infoContextual' gals = do
>     save <- get
>     let bsc = inBScope save
>     me <- getCurrentName
>     ds <- many (hypsHere bsc me <* optional killBelow <* goOut <* removeEntryAbove)
>     d <- hypsHere bsc me
>     put save
>     return (renderHouseStyle (vcat (d:reverse ds)))
>  where
>    hypsHere :: BScopeContext -> Name -> ProofState Doc
>    hypsHere bsc me = do
>        es <- getEntriesAbove
>        d <- hyps bsc me
>        putEntriesAbove es
>        return d
>    
>    killBelow = do
>        l <- getLayer
>        replaceLayer (l { belowEntries = NF F0 })
>
>    hyps :: BScopeContext -> Name -> ProofState Doc
>    hyps bsc me = do
>        es <- getEntriesAbove
>        case (gals, es) of
>            (_, B0) -> return empty
>            (False, es' :< EPARAM ref _ k _ _) -> do
>                putEntriesAbove es'
>                ty' <- bquoteHere (pty ref)
>                docTy <- prettyHere (SET :>: ty')
>                d <- hyps bsc me
>                return (d $$ prettyBKind k (text (showRelName (christenREF bsc ref)) <+> kword KwAsc <+> docTy))
>            (True, es' :< EDEF ref _ _ _ _ _) -> do
>                goIn
>                es <- getEntriesAbove
>                (ty :=>: _) <- getGoal "hyps"
>                ty' <- bquoteHere (evTm (inferGoalType es ty))
>                docTy <- prettyHere (SET :>: ty')
>                goOut
>                putEntriesAbove es'
>                d <- hyps bsc me
>                return (d $$ (text (showRelName (christenREF bsc ref)) <+> kword KwAsc <+> docTy))
>            (_, es' :< _) -> putEntriesAbove es' >> hyps bsc me


> infoScheme :: RelName -> ProofState String
> infoScheme x = do
>     (_, as, ms) <- resolveHere x
>     case ms of
>         Just sch -> do
>             d <- prettySchemeHere (applyScheme sch as)
>             return (renderHouseStyle d)
>         Nothing -> return (showRelName x ++ " does not have a scheme.")


The |infoWhatIs| command displays a term in various representations.

> infoWhatIs :: DExTmRN -> ProofState String
> infoWhatIs tmd = draftModule "__infoWhatIs" (do
>     (tm :=>: tmv :<: tyv) <- elabInfer' tmd
>     tmq <- bquoteHere tmv
>     tms :=>: _ <- distillHere (tyv :>: tmq)
>     ty <- bquoteHere tyv
>     tys :=>: _ <- distillHere (SET :>: ty)
>     return (unlines
>         [  "Parsed term:", show tmd
>         ,  "Elaborated term:", show tm
>         ,  "Quoted term:", show tmq
>         ,  "Distilled term:", show tms
>         ,  "Pretty-printed term:", renderHouseStyle (pretty tms maxBound)
>         ,  "Inferred type:", show tyv
>         ,   "Quoted type:", show ty
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
>     d <- prettyPS inScope me
>     return (renderHouseStyle d)
>
> prettyPS :: Entries -> Name -> ProofState Doc
> prettyPS aus me = do
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
>     prettyE (EPARAM (_ := DECL :<: ty) (x, _) k _ anchor)  = do
>         ty' <- bquoteHere ty
>         tyd <- prettyHereAt (pred ArrSize) (SET :>: ty')
>         return (prettyBKind k
>                  (text x  <+> (maybe empty (brackets . brackets . text) anchor)
>                           <+> kword KwAsc
>                           <+> tyd))
>      
>     prettyE e = do
>         goIn
>         d <- prettyPS aus me
>         goOut
>         return (sep  [  text (fst (entryLastName e)) 
>                         <+> (maybe empty (brackets . brackets . text) $ entryAnchor e) 
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
>             Unknown (ty :=>: _) -> do
>                 hk <- getHoleKind
>                 tyd <- prettyHere (SET :>: ty)
>                 return (prettyHKind hk <+> kword KwAsc <+> tyd)
>             Suspended (ty :=>: _) prob -> do
>                 hk <- getHoleKind
>                 tyd <- prettyHere (SET :>: ty)
>                 return (text ("(SUSPENDED: " ++ show prob ++ ")")
>                             <+> prettyHKind hk <+> kword KwAsc <+> tyd)
>             Defined tm (ty :=>: tyv) -> do
>                 tyd <- prettyHere (SET :>: ty)
>                 tmd <- prettyHereAt (pred ArrSize) (tyv :>: tm)
>                 return (tmd <+> kword KwAsc <+> tyd)

>     prettyHKind :: HKind -> Doc
>     prettyHKind Waiting     = text "?"
>     prettyHKind Hoping      = text "HOPE?"
>     prettyHKind (Crying s)  = text ("CRY <<" ++ s ++ ">>")


The |elm| Cochon tactic elaborates a term, then starts the scheduler to
stabilise the proof state, and returns a pretty-printed representation of the
final type-term pair (using a quick hack).

> elmCT :: DExTmRN -> ProofState String
> elmCT tm = do
>     suspend ("elab" :<: sigSetTM :=>: sigSetVAL) (ElabInferProb tm)
>     startScheduler
>     infoElaborate (DP [("elab", Rel 0)] ::$ [])


> import -> CochonTactics where
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term>, stabilise and print type-term pair."

>   : unaryExCT "elaborate" infoElaborate
>       "elaborate <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."
>   : unaryExCT "infer" infoInfer
>       "infer <term> - elaborates <term> and infers its type."

>   : unaryInCT "parse" (return . show)
>       "parse <term> - parses <term> and displays the internal display-sytnax representation."

>   : unaryNameCT "scheme" infoScheme
>       "scheme <name> - looks up the scheme on the definition <name>."

>   : unaryStringCT "show" (\s -> case s of
>         "inscope"  -> infoInScope
>         "context"  -> infoContext 
>         "dump"     -> infoDump
>         "hyps"     -> infoHypotheses
>         "state"    -> prettyProofState
>         _          -> return "show: please specify exactly what to show."
>       )
>       "show <inscope/context/dump/hyps/state> - displays useless information."

>   : unaryExCT "whatis" infoWhatIs
>       "whatis <term> - prints the various representations of <term>."
