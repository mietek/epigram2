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

> coreLineAction :: Bwd Entry -> CoreLine -> Dev -> Root -> Maybe (Dev, Root)
> coreLineAction gs (LLam [] _) d r = Just (d, r)
> coreLineAction gs (LLam (x : xs) mty) (es, tip) r = do
>   s <- tipDom mty tip r
>   let xr = name r x := DECL :<: s
>   let xe = E xr (x, snd r) (Boy LAMB)
>   coreLineAction gs (LLam xs mty) (es :< xe, tipRan tip xr) (roos r)
> coreLineAction gs LCom d r = Just (d, r)
> coreLineAction gs (LDef x (Just ty) tss) (es, t) r =
>   let  gs' = gs <+> es
>        vy = evTm ty
>        (d@(ds, u), tss') =
>          runWriter (makeFun gs' (B0, Unknown vy) tss (room r x))
>        xr = name r x := (case u of
>               Unknown _ -> HOLE
>               Defined b _ ->
>                 DEFN (evTm (lambda gs' (discharge ds ((gs' <+> ds) -| b))))) :<: vy
>        xe = E xr (x, snd r) (Girl LETG d)
>   in   Just ((es :< xe, t), roos r)
> coreLineAction gs (LEq (Just t) Nothing) (es, Unknown y) r = do
>   () <- check (y :>: t) r
>   Just ((es, Defined t y), r)
> coreLineAction gs (LEq (Just t) (Just y)) (es, tip) r = do
>   () <- check (SET :>: y) r
>   let vy = evTm y
>   () <- case tip of
>      Unknown y' -> guard $ equal (SET :>: (vy, y')) r
>      _ -> (|()|)
>   () <- check (vy :>: t) r
>   Just ((es, Defined t (evTm y)), r)
> coreLineAction gs (LEq Nothing Nothing) (es, Unknown y) r =
>   Just ((es, Unknown y), r)
> coreLineAction gs (LEq Nothing (Just y)) (es, tip) r = do
>   () <- check (SET :>: y) r
>   let vy = evTm y
>   () <- case tip of
>      Unknown y' -> guard $ equal (SET :>: (vy, y')) r
>      _ -> (|()|)
>   Just ((es, Unknown (evTm y)), r)
> coreLineAction _ _ _ _ = Nothing


> discharge :: Bwd Entry -> INTM -> INTM
> discharge B0 t = t
> discharge (es :< E _ _ (Girl _ _)) t = discharge es t
> discharge (es :< E _ (x, _) (Boy LAMB)) t = discharge es (L (x :. t))
> discharge (es :< E _ (x, _) (Boy (PIB s))) t = discharge es (PI x (es -| s) t)

> lambda :: Bwd Entry -> INTM -> INTM
> lambda B0 t = t
> lambda (es :< E _ _ (Girl _ _)) t = lambda es t
> lambda (es :< E _ (x, _) (Boy _)) t = lambda es (L (x :. t))

> disMangle :: Bwd Entry -> Int -> Mangle I REF REF
> disMangle ys i = Mang
>   {  mangP = \ x ies -> (|(h ys x i $:$) ies|)
>   ,  mangV = \ i ies -> (|(V i $:$) ies|)
>   ,  mangB = \ _ -> disMangle ys (i + 1)
>   } where
>   h B0                        x i  = P x
>   h (ys :< E y _ (Boy _))     x i
>     | x == y     = V i
>     | otherwise  = h ys x (i + 1)
>   h (ys :< E y _ (Girl _ _))  x i = h ys x i

> (-|) :: Bwd Entry -> INTM -> INTM
> es -| t = disMangle es 0 %% t

> tipDom :: Maybe INTM -> Tip -> Root -> Maybe TY
> tipDom (Just s)  Module                   r = do
>   () <- check (SET :>: s) r
>   return (evTm s)
> tipDom (Just s)  (Unknown (C (Pi s' _)))  r = do
>   () <- check (SET :>: s) r
>   let vs = evTm s
>   guard $ equal (SET :>: (vs, s')) r
>   return vs
> tipDom Nothing   (Unknown (C (Pi s _)))  r = Just s
> tipDom _         _                       r = Nothing

> tipRan :: Tip -> REF -> Tip
> tipRan (Unknown (C (Pi _ t)))  x  = Unknown (t $$ A (pval x))
> tipRan Module                  _  = Module

> makeFun :: Bwd Entry -> Dev -> [[Tok]] -> Root -> Writer [[Tok]] Dev
> makeFun gs d [] r = (|d|)
> makeFun gs d@(ls, _) (ts : tss) r =
>   fromMaybe (tell [Key "--" : Spc 1 : ts] >> makeFun gs d tss r) $ do
>     c <- parse (pCoreLine (gs <+> ls)) ts
>     (d, r) <- coreLineAction gs c d r
>     return (tell [ts] >> makeFun gs d tss r)

> coreLoad :: [[Tok]] -> (Dev, [[Tok]])
> coreLoad tss = runWriter (makeFun B0 (B0, Module) tss (B0, 0))
