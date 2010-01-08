\section{Display Commands}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators #-}

> module DisplayCommands where

> import Control.Applicative hiding (empty)
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

> infoElaborate :: INDTM -> ProofState String
> infoElaborate (DN tm) = do
>     makeModule "__infoElaborate"
>     goIn
>     ty :>: tm' <- elabInfer tm
>     tm'' <- bquoteHere (evTm (N tm'))
>     s <- prettyHere (ty :>: tm'')
>     goOut
>     dropModule
>     return (show s)
> infoElaborate _ = throwError' "infoElaborate: can only elaborate neutral terms."


The |infoInfer| command is similar to |infoElaborate|, but it returns a string
representation of the resulting type.

> infoInfer :: INDTM -> ProofState String
> infoInfer (DN tm) = do
>     makeModule "__infoInfer"
>     goIn
>     ty :>: _ <- elabInfer tm
>     ty' <- bquoteHere ty
>     s <- prettyHere (SET :>: ty')
>     goOut
>     dropModule
>     return (show s)
> infoInfer _ = throwError' "infoInfer: can only infer the type of neutral terms."


The |infoHypotheses| command displays a distilled list of things in the context.

> infoHypotheses :: ProofState String
> infoHypotheses = do
>     n <- getMotherName
>     aus <- getAuncles
>     me <- getMotherName
>     ds <- many (hypsHere aus me <* goOut)
>     d <- hypsHere aus me
>     goTo n
>     return (show (vcat (d:reverse ds)))
>  where
>    hypsHere :: Entries -> Name -> ProofState Doc
>    hypsHere aus me = do
>      es <- getDevEntries
>      d <- hyps aus me
>      putDevEntries es
>      return d
>
>    hyps :: Entries -> Name -> ProofState Doc
>    hyps aus me = do
>        es <- getDevEntries
>        case es of
>            B0 -> return empty
>            (es' :< E ref _ (Boy k) ty) -> do
>                putDevEntries es'
>                docTy <- prettyHere (SET :>: ty)
>                d <- hyps aus me
>                return (d $$ prettyBKind k (text (christenREF aus me ref) <+> text ":" <+> docTy))
>            (es' :< E ref _ (Girl LETG d) ty) -> do
>                goIn
>                docTy <- prettyHere (SET :>: ty)
>                goOut
>                putDevEntries es'
>                d <- hyps aus me
>                return (d $$ (text (christenREF aus me ref) <+> text ":" <+> docTy))
>            (es' :< _) -> putDevEntries es' >> hyps aus me


The |prettyHere| command distills a term in the current context,
then passes it to the pretty-printer.

> prettyHere :: (TY :>: INTM) -> ProofState Doc
> prettyHere tt = do
>     aus <- getAuncles
>     dtm :=>: _ <- distill aus tt
>     return (pretty dtm)