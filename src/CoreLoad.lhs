\section{CoreLoad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module CoreLoad where

> import Control.Monad
> import Control.Monad.Writer
> import Control.Monad.State
> import Control.Monad.Instances
> import Control.Applicative
> import Data.Char
> import Data.Maybe
> import Data.Foldable hiding (elem)
> import Data.Traversable

> import BwdFwd
> import Tm
> import Lexer
> import Parsley
> import TmParse
> import Core
> import Root

%endif

> data Offs = Rel Int | Abs Int deriving Show

> noffer :: Char -> Bool
> noffer c = not (elem c ".^_")

> offs :: P Char Offs
> offs =
>   (|Abs {teq '_'} (|read (some (tok isDigit))|)
>    |Rel {teq '^'} (|read (some (tok isDigit))|)
>    |(Rel 0)
>    |)

> type RelName = [(String,Offs)]

> relName :: P Char [(String,Offs)]
> relName = pSep (teq '.') (|some (tok noffer), offs|)

> vinc :: ExTm REF -> ExTm REF
> vinc (V i)  = V (i + 1)
> vinc n      = n

> hits :: (String, Int) -> (String, Offs) -> Either (String, Offs) ()
> hits (x, i) (y, o) | x == y = case o of
>   Abs j | i == j  -> Right ()
>   Rel 0           -> Right ()
>   Rel j           -> Left (y, Rel (j - 1))
> hits _ yo = Left yo

> boy :: Entry -> Spine {TT} REF
> boy (E r _ (Boy _))  = [A (N (P r))]
> boy _                = []

> findC :: REF -> Spine {TT} REF -> Entity -> RelName -> Maybe (ExTm REF)
> findC r  as (Boy _)           []  = (|(P r)|)
> findC r  as _                 []  = (|(P r $:$ as)|)
> findC r  as (Girl _ (es, _))  ys  = findD es ys as
> findC _  as _                 ys  = empty

> findD :: Bwd Entry -> RelName -> Spine {TT} REF -> Maybe (ExTm REF)
> findD B0 sos as = empty
> findD (xs :< E r x e@(Girl _ _)) (y : ys) as = case hits x y of
>   Right _  -> findC r as e ys
>   Left y'  -> findD xs (y' : ys) as

> findG :: Bwd Entry -> RelName -> Maybe (ExTm REF)
> findG B0 sos = empty
> findG (xs :< E r x e) (y : ys) = case hits x y of
>   Right _  -> findC r (foldMap boy xs) e ys
>   Left y'  -> findG xs (y' : ys)

> findL :: Bwd Entry -> Bwd String -> RelName -> Maybe (ExTm REF)
> findL ps B0 sos = findG ps sos
> findL ps (xs :< x) [(y, Rel 0)]       | x == y = (|(V 0)|)
> findL ps (xs :< x) ((y, Rel i) : sos) | x == y =
>   vinc <$> findL ps xs ((y, Rel (i - 1)) : sos)
> findL ps (xs :< x) sos = vinc <$> findL ps xs sos

> resolve :: Bwd Entry -> Bwd String -> Mangle Maybe String REF
> resolve ps vs = Mang
>   {  mangP = \ x mes -> (|(|(findL ps vs) (parse relName x) @ |) $:$ mes|)
>   ,  mangV = \ _ _ -> Nothing -- what's that index doing here?
>   ,  mangB = \ x -> resolve ps (vs :< x)
>   } where

> auncles :: WhereAmI -> Bwd Entry
> auncles (ls, _, (es, _)) = foldMap elders ls <+> es

> testResolve :: Tm {In, TT} String -> Maybe (Tm {In, TT} REF)
> testResolve t = resolve B0 B0 % t

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap

> pINTM :: Bwd Entry -> P Tok INTM
> pINTM es = grok (resolve es B0 %) bigTmIn

> data CoreLine
>   = LLam [String]
>   | LCom

> pCoreLine :: Bwd Entry -> P Tok CoreLine
> pCoreLine es =
>   (|LLam {key "\\"} (some idf)
>    |LCom {key "--"; pRest}|)

> coreLineAction :: CoreLine -> Dev -> Root -> Maybe (Dev, Root)
> coreLineAction (LLam []) d r = Just (d, r)
> coreLineAction (LLam (x : xs)) (es, Unknown (C (Pi s t))) r =
>   coreLineAction (LLam xs) (es :< xe, Unknown (t $$ A (pval xr))) (roos r) where
>     xr = name r x := DECL s
>     xe = E xr (x, snd r) (Boy LAMB)
> coreLineAction LCom d r = Just (d, r)

> makeFun :: Bwd Entry -> Dev -> [[Tok]] -> Root -> Writer [[Tok]] Dev
> makeFun gs d [] r = (|d|)
> makeFun gs d@(ls, _) (ts : tss) r =
>   fromMaybe (tell [Key "--" : Spc 1 : ts] >> makeFun gs d tss r) $ do
>     c <- parse (pCoreLine (gs <+> ls)) ts
>     (d, r) <- coreLineAction c d r
>     return (tell [ts] >> makeFun gs d tss r)

> instance Monoid o => Applicative (Writer o) where
>   pure = return
>   (<*>) = ap
