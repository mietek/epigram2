\section{DevLoad}

This module provides functionality for resolving names (converting an
|InTm String| produced by |TmParse| into an |INTM|) and hence for
loading developments.

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module DevLoad (devLoad, parseTerm) where

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
> import Layout
> import Lexer
> import MissingLibrary
> import Parsley
> import TmParse
> import Developments
> import Root
> import Rules

%endif

> data Offs = Rel Int | Abs Int deriving Show

> noffer :: Char -> Bool
> noffer c = not (elem c ".^_")

> offs :: P Char Offs
> offs =
>   (|Abs (%teq '_'%) (|read (some (tok isDigit))|)
>    |Rel (%teq '^'%) (|read (some (tok isDigit))|)
>    |(Rel 0)
>    |)

> type RelName = [(String,Offs)]

> relName :: P Char [(String,Offs)]
> relName = pSep (teq '.') (|some (tok noffer), offs|)



> hits :: (String, Int) -> (String, Offs) -> Either (String, Offs) ()
> hits (x, i) (y, o) | x == y = case o of
>   Abs j | i == j  -> Right ()
>   Rel 0           -> Right ()
>   Rel j           -> Left (y, Rel (j - 1))
> hits _ yo = Left yo

> boy :: Entry -> Spine {TT} REF
> boy (E r _ (Boy _) _)  = [A (N (P r))]
> boy _                = []

> findC :: REF -> Spine {TT} REF -> Entity -> RelName -> Maybe (ExTm REF)
> findC r  as (Boy _)           []  = (|(P r)|)
> findC r  as _                 []  = (|(P r $:$ as)|)
> findC r  as (Girl _ (es, _, _))  ys  = findD es ys as
> findC _  as _                 ys  = empty

> findD :: Bwd Entry -> RelName -> Spine {TT} REF -> Maybe (ExTm REF)
> findD B0 sos as = empty
> findD (xs :< E r x e@(Girl _ _) _) (y : ys) as = case hits x y of
>   Right _  -> findC r as e ys
>   Left y'  -> findD xs (y' : ys) as

> findG :: Bwd Entry -> RelName -> Maybe (ExTm REF)
> findG B0 sos = empty
> findG (xs :< E r x e _) (y : ys) = case hits x y of
>   Right _  -> findC r (foldMap boy xs) e ys
>   Left y'  -> findG xs (y' : ys)

> findL :: Bwd Entry -> Bwd String -> RelName -> Maybe (ExTm REF)
> findL ps B0 sos = findG ps sos
> findL ps (xs :< x) [(y, Rel 0)]       | x == y = (|(V 0)|)
> findL ps (xs :< x) ((y, Rel i) : sos) | x == y =
>   vinc <$> findL ps xs ((y, Rel (i - 1)) : sos)
> findL ps (xs :< x) sos = vinc <$> findL ps xs sos

> vinc :: ExTm REF -> ExTm REF
> vinc (V i)  = V (i + 1)
> vinc n      = n


The |resolve| function takes a context and a list of binder names, and
produces a mangler that, when applied, attempts to resolve the parameter
names in an |InTm String| to produce an |InTm REF|.

> resolve :: Bwd Entry -> Bwd String -> Mangle Maybe String REF
> resolve ps vs = Mang
>   {  mangP = \ x mes -> (|(|(findL ps vs) (parse relName x) @ |) $:$ mes|)
>   ,  mangV = \ _ _ -> Nothing -- what's that index doing here?
>   ,  mangB = \ x -> resolve ps (vs :< x)
>   } where

> testResolve :: InTm String -> Maybe INTM
> testResolve t = resolve B0 B0 % t


The |pINTM| function produces a parser for terms, given a context, by resolving
in the context all the names in the |InTm String| produced by |bigTmIn|.

> pINTM :: Bwd Entry -> P Tok INTM
> pINTM es = grok (resolve es B0 %) bigTmIn


> data CoreLine
>   = LLam [String] (Maybe INTM)
>   | LDef String (Maybe INTM) [[Tok]]
>   | LEq (Maybe INTM) (Maybe INTM)
>   | LCom
>   deriving Show

> pCoreLine :: Bwd Entry -> P Tok CoreLine
> pCoreLine es =
>   (|LLam (%key "\\"%) (some idf) (%spc%) (optional (pINTM es))
>    |LCom (%key "--"; pRest%)
>    |LDef idf (optional (key ":" >> pINTM es)) (lay "where" pRest)
>    |LEq (%key "="%) (|Nothing (%key "?"%) | Just (pINTM es)|)
>         (optional (key ":" >> pINTM es))
>    |LCom (%pSep (tok isSpcT) (teq Sem)%)
>    |)


The |coreLineAction| function takes a context, a |CoreLine| and a current
development. It attempts to update the development with the information
from the |CoreLine|, producing |Nothing| if this fails.

> coreLineAction :: Bwd Entry -> CoreLine -> Dev -> Maybe Dev
> coreLineAction gs (LLam [] _) d = Just d
> coreLineAction gs (LLam (x : xs) mty) (es, tip, r) = do
>   (st :=>: s) <- tipDom mty tip r
>   let xr = name r x := DECL :<: s
>   let xe = E xr (x, snd r) (Boy LAMB) st
>   coreLineAction gs (LLam xs mty) (es :< xe, tipRan tip xr r, roos r)
> coreLineAction gs LCom d = Just d
> coreLineAction gs (LDef x (Just ty) tss) (es, t, r) =
>   let  gs' = gs <+> es
>        vy = evTm ty
>        (d@(ds, u, _), tss') =
>          runWriter (makeFun gs' (B0, Unknown (ty :=>: vy), room r x) tss)
>        xr = name r x := (case u of
>               Unknown _ -> HOLE
>               Defined b _ ->
>                 DEFN (evTm (parBind gs' ds b))) :<: vy
>        xe = E xr (x, snd r) (Girl LETG d) ty
>   in   Just (es :< xe, t, roos r)
> coreLineAction gs (LEq (Just t) Nothing) (es, Unknown (u :=>: y), r) = do
>   () <- check (y :>: t) r
>   Just (es, Defined t (u :=>: y), r)
> coreLineAction gs (LEq (Just t) (Just y)) (es, tip, r) = do
>   () <- check (SET :>: y) r
>   let vy = evTm y
>   () <- case tip of
>      Unknown (_ :=>: y') -> guard $ equal (SET :>: (vy, y')) r
>      _ -> (|()|)
>   () <- check (vy :>: t) r
>   Just (es, Defined t (y :=>: evTm y), r)
> coreLineAction gs (LEq Nothing Nothing) (es, Unknown y, r) =
>   Just (es, Unknown y, r)
> coreLineAction gs (LEq Nothing (Just y)) (es, tip, r) = do
>   () <- check (SET :>: y) r
>   let vy = evTm y
>   () <- case tip of
>      Unknown (_ :=>: y') -> guard $ equal (SET :>: (vy, y')) r
>      _ -> (|()|)
>   Just (es, Unknown (y :=>: evTm y), r)
> coreLineAction _ _ _ = Nothing


> tipDom :: Maybe INTM -> Tip -> Root -> Maybe (INTM :=>: TY)
> tipDom (Just s)  Module                   r = do
>   () <- check (SET :>: s) r
>   return (s :=>: evTm s)
> tipDom (Just s)  (Unknown (_ :=>: PI s' _))  r = do
>   () <- check (SET :>: s) r
>   let vs = evTm s
>   guard $ equal (SET :>: (vs, s')) r
>   return (s :=>: vs)
> tipDom Nothing   (Unknown (_ :=>: PI s _))  r = Just (bquote B0 s r :=>: s)
> tipDom _         _                          r = Nothing


The |tipRan| function applies the $\Pi$-type at the |Unknown| tip to the given
reference, and returns an |Unknown| tip with the resulting type. If the tip
is a |Module|, it is returned unchanged.

> tipRan :: Tip -> REF -> Root -> Tip
> tipRan (Unknown (ty :=>: PI _ t))  x r  = let tyv = t $$ A (pval x) in
>   Unknown (bquote B0 tyv r :=>: tyv)
> tipRan Module                      _ _  = Module


The |makeFun| function takes a context, a development produced so far and a list
of lists of tokens. It attempts to interpret each list of tokens to update the
development, and writes out an updated list of lists of tokens with those that
fail commented out.

> makeFun :: Bwd Entry -> Dev -> [[Tok]] -> Writer [[Tok]] Dev
> makeFun gs d [] = (|d|)
> makeFun gs d@(ls, _, r) (ts : tss) =
>   fromMaybe (tell [Key "--" : Spc 1 : ts] >> makeFun gs d tss) $ do
>     c <- parse (pCoreLine (gs <+> ls)) ts
>     d <- coreLineAction gs c d
>     return (tell [ts] >> makeFun gs d tss)


The |devLoad| function takes a |[[Tok]]| as produced by |layout|, and converts it
to a |Module| development. It returns the |Dev| produced, and a
|[[Tok]]| with any lines that fail to type-check commented out.

> devLoad :: [[Tok]] -> (Dev, [[Tok]])
> devLoad tss = runWriter (makeFun B0 (B0, Module, (B0, 0)) tss)


We should replace |parseTerm| once we having parsing sorted out.
\question{Should this really just take the second entry in the list?}

> parseTerm :: String -> Bwd Entry -> Maybe INTM
> parseTerm s es = case layout . tokenize $ s of 
>   (_:x:_)  -> parse (pINTM es) x
>   _        -> Nothing