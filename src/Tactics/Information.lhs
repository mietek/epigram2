\section{Presenting Information}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module Tactics.Information where

> import Control.Applicative hiding (empty)
> import Control.Monad.State
> import Text.PrettyPrint.HughesPJ

> import Kit.BwdFwd hiding ((<+>))

> import ProofState.Developments
> import ProofState.Lifting
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Distiller
> import DisplayLang.Elaborator
> import DisplayLang.Lexer
> import DisplayLang.Naming
> import DisplayLang.PrettyPrint

> import NameSupply.NameSupply

> import Evidences.Rules hiding (($$))
> import Evidences.Tm

%endif


The |infoElaborate| command calls |elabInfer| on the given neutral display term,
evaluates the resulting term, bquotes it and returns a pretty-printed string
representation. Note that it works in its own module which it discards at the
end, so it will not leave any subgoals lying around in the proof state.

> infoElaborate :: ExDTmRN -> ProofState String
> infoElaborate tm = do
>     makeModule "__infoElaborate"
>     goIn
>     (tm' :=>: tmv :<: ty, _) <- elabInfer tm
>     tm'' <- bquoteHere tmv
>     s <- prettyHere (ty :>: tm'')
>     goOut
>     dropModule
>     return (renderHouseStyle s)


The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: ExDTmRN -> ProofState String
> infoInfer tm = do
>     makeModule "__infoInfer"
>     goIn
>     (_ :<: ty, _) <- elabInfer tm
>     ty' <- bquoteHere ty
>     s <- prettyHere (SET :>: ty')
>     goOut
>     dropModule
>     return (renderHouseStyle s)


The |infoContextual| command displays a distilled list of things in the context,
boys if the argument is False or girls if the argument is True.
This is written using a horrible imperative hack that saves the state, throws
away bits of the context to produce an answer, then restores the saved state.

> infoHypotheses  = infoContextual False
> infoContext     = infoContextual True

> infoContextual :: Bool -> ProofState String
> infoContextual gals = do
>     save <- get
>     aus <- getAuncles
>     me <- getMotherName
>     ds <- many (hypsHere aus me <* optional killCadets <* goOut <* removeDevEntry)
>     d <- hypsHere aus me
>     put save
>     return (renderHouseStyle (vcat (d:reverse ds)))
>  where
>    hypsHere :: Entries -> Name -> ProofState Doc
>    hypsHere aus me = do
>        es <- getDevEntries
>        d <- hyps aus me
>        putDevEntries es
>        return d
>    
>    killCadets = do
>        l <- getLayer
>        replaceLayer (l { cadets = NF F0 })
>
>    hyps :: Entries -> Name -> ProofState Doc
>    hyps aus me = do
>        es <- getDevEntries
>        case (gals, es) of
>            (_, B0) -> return empty
>            (False, es' :< E ref _ (Boy k) _) -> do
>                putDevEntries es'
>                ty' <- bquoteHere (pty ref)
>                docTy <- prettyHere (SET :>: ty')
>                d <- hyps aus me
>                return (d $$ prettyBKind k (text (showRelName (christenREF aus me ref)) <+> kword KwAsc <+> docTy))
>            (True, es' :< E ref _ (Girl LETG _ _) _) -> do
>                goIn
>                es <- getDevEntries
>                (ty :=>: _) <- getGoal "hyps"
>                ty' <- bquoteHere (evTm (inferGoalType es ty))
>                docTy <- prettyHere (SET :>: ty')
>                goOut
>                putDevEntries es'
>                d <- hyps aus me
>                return (d $$ (text (showRelName (christenREF aus me ref)) <+> kword KwAsc <+> docTy))
>            (_, es' :< _) -> putDevEntries es' >> hyps aus me


The |infoWhatIs| command displays a term in various representations.

> infoWhatIs :: ExDTmRN -> ProofState String
> infoWhatIs tmd = draftModule "__infoWhatIs" (do
>     (tm :=>: tmv :<: tyv, _) <- elabInfer tmd
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


The |distillHere| command distills a term in the current context.

> distillHere :: (TY :>: INTM) -> ProofState (InDTmRN :=>: VAL)
> distillHere tt = do
>     aus <- getAuncles
>     mliftError $ distill aus tt
>         where mliftError :: ProofStateT INTM a -> ProofState a
>               mliftError = mapStateT liftError


The |prettyHere| command distills a term in the current context,
then passes it to the pretty-printer.

> prettyHere :: (TY :>: INTM) -> ProofState Doc
> prettyHere = prettyHereAt maxBound

> prettyHereAt :: Size -> (TY :>: INTM) -> ProofState Doc
> prettyHereAt size tt = do
>     dtm :=>: _ <- distillHere tt
>     return (pretty dtm size)

The |resolveHere| command resolves a relative name to a reference,
discarding any shared parameters it should be applied to.

> resolveHere :: RelName -> ProofState REF
> resolveHere x = elabResolve x >>= (\ (r, _, _) -> return r)


The |prettyProofState| command generates a pretty-printed representation
of the proof state at the current location.

> prettyProofState :: ProofState String
> prettyProofState = do
>     aus <- getAuncles
>     me <- getMotherName
>     d <- prettyPS aus me
>     return (renderHouseStyle d)
>
> prettyPS :: Entries -> Name -> ProofState Doc
> prettyPS aus me = do
>         es <- replaceDevEntries B0
>         case es of
>             B0 -> prettyEmptyTip
>             _ -> do
>                 d <- prettyEs empty (es <>> F0)
>                 tip <- prettyTip
>                 return (lbrack <+> d $$ rbrack <+> tip)
>  where
>     prettyEs :: Doc -> Fwd (Entry Bwd) -> ProofState Doc
>     prettyEs d F0         = return d
>     prettyEs d (e :> es) = do
>         putDevEntry e
>         ed <- prettyE e
>         prettyEs (d $$ ed) es
>
>     prettyE (E (_ := DECL :<: ty) (x, _) (Boy k) _)  = do
>         ty' <- bquoteHere ty
>         tyd <- prettyHereAt (pred ArrSize) (SET :>: ty')
>         return (prettyBKind k
>                  (text x <+> kword KwAsc <+> tyd))
>                                       
>     prettyE e = do
>         goIn
>         d <- prettyPS aus me
>         goOut
>         return (sep  [  text (fst (entryLastName e))
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
>                 tyd <- prettyHere (SET :>: ty)
>                 return (char '?' <+> kword KwAsc <+> tyd)
>             Defined tm (ty :=>: tyv) -> do
>                 tyd <- prettyHere (SET :>: ty)
>                 tmd <- prettyHereAt (pred ArrSize) (tyv :>: tm)
>                 return (tmd <+> kword KwAsc <+> tyd)


> import -> CochonTactics where
>   : unaryExCT "elaborate" infoElaborate
>       "elaborate <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."
>   : unaryExCT "infer" infoInfer
>       "infer <term> - elaborates <term> and infers its type."

>   : unaryInCT "parse" (return . show)
>       "parse <term> - parses <term> and displays the internal display-sytnax representation."

>   : unaryStringCT "show" (\s -> case s of
>         "auncles"  -> infoAuncles
>         "context"  -> infoContext 
>         "dump"     -> infoDump
>         "hyps"     -> infoHypotheses
>         "state"    -> prettyProofState
>         _          -> return "show: please specify exactly what to show."
>       )
>       "show <auncles/context/dump/hyps/state> - displays useless information."

>   : unaryExCT "whatis" infoWhatIs
>       "whatis <term> - prints the various representations of <term>."
