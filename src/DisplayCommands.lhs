\section{Display Commands}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module DisplayCommands where

> import Control.Applicative hiding (empty)
> import Control.Monad.State
> import Text.PrettyPrint.HughesPJ

> import BwdFwd hiding ((<+>))
> import Developments
> import DisplayTm
> import Distiller
> import Elaborator
> import MissingLibrary
> import Naming
> import PrettyPrint
> import ProofState
> import Root
> import Rooty
> import Rules hiding (($$))
> import Tm

%endif


The |infoElaborate| command calls |elabInfer| on the given neutral display term,
evaluates the resulting term, bquotes it and returns a pretty-printed string
representation. Note that it works in its own module which it discards at the
end, so it will not leave any subgoals lying around in the proof state.

> infoElaborate :: EXDTM -> ProofState String
> infoElaborate tm = do
>     makeModule "__infoElaborate"
>     goIn
>     ty :>: tm' <- elabInfer tm
>     tm'' <- bquoteHere (evTm (N tm'))
>     s <- prettyHere (ty :>: tm'')
>     goOut
>     dropModule
>     return (renderHouseStyle s)


The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: EXDTM -> ProofState String
> infoInfer tm = do
>     makeModule "__infoInfer"
>     goIn
>     ty :>: _ <- elabInfer tm
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
>                return (d $$ prettyBKind k (text (christenREF aus me ref) <+> text ":" <+> docTy))
>            (True, es' :< E ref _ (Girl LETG _) _) -> do
>                goIn
>                es <- getDevEntries
>                (ty :=>: _) <- getGoal "hyps"
>                ty' <- bquoteHere (evTm (inferGoalType es ty))
>                docTy <- prettyHere (SET :>: ty')
>                goOut
>                putDevEntries es'
>                d <- hyps aus me
>                return (d $$ (text (christenREF aus me ref) <+> text ":" <+> docTy))
>            (_, es' :< _) -> putDevEntries es' >> hyps aus me


The |infoWhatIs| command displays a term in various representations.

> infoWhatIs :: EXDTM -> ProofState String
> infoWhatIs tmd = draftModule "__infoWhatIs" (do
>     (tyv :>: tm) <- elabInfer tmd
>     tmq <- bquoteHere (evTm tm)
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

> distillHere :: (TY :>: INTM) -> ProofState (InDTm String :=>: VAL)
> distillHere tt = do
>     aus <- getAuncles
>     distill aus tt

The |prettyHere| command distills a term in the current context,
then passes it to the pretty-printer.

> prettyHere :: (TY :>: INTM) -> ProofState Doc
> prettyHere tt = do
>     dtm :=>: _ <- distillHere tt
>     return (pretty dtm maxBound)


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
>         tyd <- prettyHere (SET :>: ty')
>         return (prettyBKind k
>                  (text x <+> colon <+> tyd))
>                                       
>     prettyE e = do
>         goIn
>         d <- prettyPS aus me
>         goOut
>         return (sep  [  text (fst (entryLastName e))
>                      ,  nest 2 d <+> semi
>                      ])
>
>     prettyEmptyTip :: ProofState Doc
>     prettyEmptyTip = do
>         tip <- getDevTip
>         case tip of
>             Module -> return (brackets empty)
>             _ -> do
>                 tip <- prettyTip
>                 return (text ":=" <+> tip)

>     prettyTip :: ProofState Doc
>     prettyTip = do
>         tip <- getDevTip
>         case tip of
>             Module -> return empty
>             Unknown (ty :=>: _) -> do
>                 tyd <- prettyHere (SET :>: ty)
>                 return (text "? :" <+> tyd)
>             Defined tm (ty :=>: tyv) -> do
>                 tyd <- prettyHere (SET :>: ty)
>                 tmd <- prettyHere (tyv :>: tm)
>                 return (tmd <+> text ":" <+> tyd)