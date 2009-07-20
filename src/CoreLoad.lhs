\section{CoreLoad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module CoreLoad where

> import Control.Monad
> import Control.Monad.State
> import Control.Applicative
> import Data.Char
> import Data.Foldable hiding (elem)
> import Data.Traversable

> import BwdFwd
> import Tm
> import Lexer
> import Parsley
> import TmParse
> import Core

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

> load :: [[Tok]] -> Construct [[Tok]]
> load [] = (|[]|)
> load (ts@(Key "--" : _) : tss) = (|(ts :) (load tss)|)

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

> findC :: REF -> Entity -> RelName -> Maybe (ExTm REF)
> findC r  _                 []  = (|(P r)|)
> findC r  (Girl _ (es, _))  ys  = findG es ys
> findC _  _                 ys  = empty

> findG :: Bwd Entry -> RelName -> Maybe (ExTm REF)
> findG B0 sos = empty
> findG (xs :< E r x e) (y : ys) = case hits x y of
>   Right _  -> ($:$ foldMap boy xs) <$> findC r e ys
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
> testResolve t = resolve (B0, (B0, 0), (B0, Module)) % t

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap

> pINTM :: Bwd Entry -> P Tok INTM
> pINTM es = grok (resolve es B0) bigTmIn

> mkLam :: String -> Maybe INTM -> Construct ()
> mkLam x _ = do
>   (ls, _, (es, Unknown (PI _ s t))) <- get
>   put (ls, (es :< E 

> action :: Bwd Entry -> P Tok Dev
> action es =
>   (|() {key "--"; pRest}
>    |() {pSep (teq Sem) spc}
>    |mkLam {key "\\"} idf {spc ; optional (pINTM es)}
>    |mkPi (pBr Rnd (|idf , {key ":"} bigTmIn|))
>    |mkDef
>       idf {spc}
>       (bra Rnd (pSep (pad (teq Sem)) (|idf, {key ":"} (pINTM es)|)))
>       {key "="} (|Just (pINTM es) | Nothing {key "?"}|)
>       {key ":"} (pInTm es)
>    |)

> coreAct :: Bwd Entry -> [Tok] -> ([Tok], Dev)
> coreAct ts = do
>   es   <- gets auncles
>   case parse (action es) ts of
>     Just a   -> (|{a} ts|)
>     Nothing  -> (|(Key "--" : Spc " " : ts)|)

> coreLoad :: [[Tok]] -> State WhereAmI [[Tok]]
> coreLoad = traverse coreAct
