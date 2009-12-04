\section{Loading Developments}

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

> import MissingLibrary
> import BwdFwd
> import Tm
> import Lexer
> import MissingLibrary
> import Naming
> import Parsley
> import TmParse
> import Developments
> import Root
> import Rules

%endif

\subsection{Resolving Local Longnames}

For display and storage purposes, we have a system of local longnames
for referring to entries. We need to resolve those names as
references. We resolve \(f.x.y.z\) by searching outwards for $f$, then
inwards for a child $x$, $x$'s child $y$, $y$'s child $z$. References
are fully $\lambda$-lifted, but as $f$'s parameters are held in common
with the point of reference, we automatically supply them.

> offs :: P Char Offs
> offs =
>   (|Abs (%teq '_'%) (|read (some (tok isDigit))|)
>    |Rel (%teq '^'%) (|read (some (tok isDigit))|)
>    |(Rel 0)
>    |)

> data Offs = Rel Int | Abs Int deriving Show
> type RelName = [(String,Offs)]

> relName :: P Char [(String,Offs)]
> relName = pSep (teq '.') (|some (tok noffer), offs|)

The |resolve| function takes a context and a list of binder names, and
produces a mangler that, when applied, attempts to resolve the parameter
names in an |InTm String| to produce an |InTm REF|, i.e.\ an INTM.

> resolve :: Bwd Entry -> Bwd String -> Mangle Maybe String REF
> resolve ps vs = Mang
>     {  mangP  = \ x mes -> (|(|(findLocal ps vs) (parse pRelName x) @ |) $:$ mes|)
>     ,  mangV  = \ _ _ -> Nothing -- what's that index doing here?
>     ,  mangB  = \ x -> resolve ps (vs :< x)
>     }
>   where
>     pRelName :: P Char RelName
>     pRelName = pSep (teq '.') (|some (tok noffer), offs|)
>
>     offs :: P Char Offs
>     offs =
>         (|Abs (%teq '_'%) (|read (some (tok isDigit))|)
>          |Rel (%teq '^'%) (|read (some (tok isDigit))|)
>          |(Rel 0)
>          |)
>
>     noffer :: Char -> Bool
>     noffer c = not (elem c ".^_")

> testResolve :: InTm String -> Maybe INTM
> testResolve t = resolve B0 B0 % t


The |pINTM| function produces a parser for terms, given a context, by resolving
in the context all the names in the |InTm String| produced by |bigTmIn|.

> pINTM :: Bwd Entry -> P Tok INTM
> pINTM es = grok (resolve es B0 %) bigTmIn


The |hits| function determines whether a name component matches a
relative name component. It returns |Right ()| if this is the right
name, and |Left x| if the search should continue (to the left) with
new relative name component |x|. (Changing the component allows its
index to be decremented if it is relative.)

> hits :: (String, Int) -> (String, Offs) -> Either (String, Offs) ()
> hits (x, i) (y, o) | x == y = case o of
>   Abs j  | i == j     -> Right  ()
>          | otherwise  -> Left   (y, o)
>   Rel 0               -> Right  ()
>   Rel j               -> Left   (y, Rel (j - 1))
> hits _ yo = Left yo


The |findLocal| function takes a context, a list of binder names and a relative
name to resolve. It first searches the binders for a |Rel| name, and
returns a de Brujin indexed variable if it is present. Otherwise, it calls
|findGlobal| to search the context.

> findLocal :: Bwd Entry -> Bwd String -> RelName -> Maybe (ExTm REF)
> findLocal ps B0 sos = findGlobal ps sos
> findLocal ps (xs :< x) [(y, Rel 0)]       | x == y = (|(V 0)|)
> findLocal ps (xs :< x) ((y, Rel i) : sos) | x == y =
>   vinc <$> findLocal ps xs ((y, Rel (i - 1)) : sos)
> findLocal ps (xs :< x) sos = vinc <$> findLocal ps xs sos
>
> vinc :: EXTM -> EXTM
> vinc (V i)  = V (i + 1)
> vinc n      = n


The |findGlobal| function takes a context and a relative name to resolve. It
searches the context for an entry that hits the name, then searches that
entry's children to resolve the next component. 

> resolve :: Bwd Entry -> Bwd String -> Mangle Maybe String REF
> resolve ps vs = Mang
>   {  mangP = \ x mes -> (|(|(findL ps vs) (parse relName x) @ |) $:$ mes|)
>   ,  mangV = \ _ _ -> Nothing -- what's that index doing here?
>   ,  mangB = \ x -> resolve ps (vs :< x)
>   } where


The |findChild| function takes a reference to a containing entry, a spine of
shared parameters, an entity |e| and the remainder of a relative name to
resolve. If the remainder is empty, it returns a parameter referring to the
current entry (applied to the shared parameters if appropriate). Otherwise,
the entity should be a |Girl|, and it searches her children for the name.

> findChild :: REF -> Spine {TT} REF -> Entity -> RelName -> Maybe EXTM
> findChild r  as (Boy _)              []  = (|(P r)|)
> findChild r  as (Girl _ _)           []  = (|(P r $:$ as)|)
> findChild r  as (Boy _)              ys  = empty
> findChild r  as (Girl _ (es, _, _))  ys  = findD es ys as
>   where
>     findD :: Bwd Entry -> RelName -> Spine {TT} REF -> Maybe EXTM
>     findD B0 sos as = empty
>     findD (xs :< E r x e@(Girl _ _) _) (y : ys) as = case hits x y of
>         Right _  -> findChild r as e ys
>         Left y'  -> findD xs (y' : ys) as

> pINTM :: Bwd Entry -> P Tok INTM
> pINTM es = grok (resolve es B0 %) bigTmIn

\subsection{Loading Developments}

> data CoreLine
>   = LLam [String] (Maybe INTM)
>   | LDef String (Maybe INTM) [[Token]]
>   | LEq (Maybe INTM) (Maybe INTM)
>   | LCom
>   deriving Show

> pCoreLine :: Bwd Entry -> Parsley Token CoreLine
> pCoreLine es =
>   (|LLam (%keyword "\\"%) (some ident) (optional (pINTM es))
>    |LCom (%keyword "--"; pRest%)

%if false

> -- FIX (or not):  |LDef ident (optional (keyword ":" >> pINTM es)) (keyword "where" *> pRest)

%endif

>    |LEq (%keyword "="%) (|Nothing (%keyword "?"%) | Just (pINTM es)|)
>         (optional (keyword ":" >> pINTM es))
>    |LCom (% many (keyword ";") %)
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
> tipDom (Just s)  Module                      r = do
>   () <- check (SET :>: s) r
>   return (s :=>: evTm s)
> tipDom (Just s)  (Unknown (_ :=>: PI s' _))  r = do
>   () <- check (SET :>: s) r
>   let vs = evTm s
>   guard $ equal (SET :>: (vs, s')) r
>   return (s :=>: vs)
> tipDom Nothing   (Unknown (_ :=>: PI s _))   r = Just (bquote B0 s r :=>: s)
> tipDom _         _                           r = Nothing


The |tipRan| function applies the $\Pi$-type at the |Unknown| tip to the given
reference, and returns an |Unknown| tip with the resulting type. If the tip
is a |Module|, it is returned unchanged.

> tipRan :: Tip -> REF -> Root -> Tip
> tipRan (Unknown (ty :=>: PI _ t))  x r  = let tyv = t $$ A (pval x) in
>   Unknown (bquote B0 tyv r :=>: tyv)
> tipRan Module                      _ _  = Module

> makeFun :: Bwd Entry -> Dev -> [[Tok]] -> Writer [[Tok]] Dev
> makeFun gs d [] = (|d|)
> makeFun gs d@(ls, _, r) (ts : tss) =
>   fromMaybe (tell [Keyword "--" : ts] >> makeFun gs d tss) $ do
>     c <- either (const Nothing) Just $ parse (pCoreLine (gs <+> ls)) ts
>     d <- coreLineAction gs c d
>     return (tell [ts] >> makeFun gs d tss)
>            

The |devLoad| function takes a |[[Token]]| as produced by |layout|, and converts it
to a |Module| development. It returns the |Dev| produced, and a
|[[Token]]| with any lines that fail to type-check commented out.

> devLoad :: [[Token]] -> (Dev, [[Token]])
> devLoad tss = error "DevLoad: Broken for political reasons. -- Pierre"
>   --runWriter (makeFun B0 (B0, Module, (B0, 0)) tss)


We should replace |parseTerm| once we having parsing sorted out.
\question{Should this really just take the second entry in the list?}

> parseTerm :: String -> Bwd Entry -> Maybe INTM
> parseTerm s es = parse (pINTM es) . (!! 1) . layout . tokenize $ s