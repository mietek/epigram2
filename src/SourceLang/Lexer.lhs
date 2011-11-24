> {-# LANGUAGE PatternGuards, FlexibleInstances #-}

> module SourceLang.Lexer where

> import Prelude hiding (foldl, all)
> import Data.List hiding (foldl, all)
> import Data.Foldable hiding (elem)
> import Control.Applicative
> import Data.Monoid

> import Kit.MissingLibrary
> import Kit.BwdFwd

> data STok = Spc Int | Sym String | Open BType | Close BType
>   deriving (Show, Eq)

> type BType = (Bracket, Maybe String)
> data Bracket = Round | Square | Curly deriving (Show, Eq)

> closes :: BType -> BType -> Bool
> closes (b, Nothing) (b', Nothing) = b == b'
> closes (b, Just s) (b', Just "") = b == b'
> closes (b, Just s) (b', Just s') = b == b' && s == s'
> closes _ _ = False

> openers :: [(Char, Bracket)]
> openers = [('(', Round), ('[', Square), ('{', Curly)]

> closers :: [(Char, Bracket)]
> closers = [(')', Round), (']', Square), ('}', Curly)]

> stok :: STok -> String
> stok (Spc i)          = replicate i ' '
> stok (Sym s)          = s
> stok (Open (b, ms))   = [op] ++ maybe "" (++ "|") ms where
>   Just op = lookup b (map swap openers)
> stok (Close (b, ms))  = maybe "" (++ "|") ms ++ [cl] where
>   Just cl = lookup b (map swap closers)

> soloists :: [Char]
> soloists = "\n\r\t,;!."

> special :: [Char]
> special = " |" ++ soloists ++ map fst openers ++ map fst closers

> boring :: Char -> Bool
> boring c = not (elem c special)

> slex1 :: Char -> String -> (STok, String)
> slex1 c s =
>   case (elem c soloists, lookup c openers, lookup c closers) of
>     (True, _, _) -> (Sym [c], s)
>     (_, Just b, _)
>       | (t, '|' : u) <- span boring s -> (Open (b, Just t), u)
>       | otherwise -> (Open (b, Nothing), s)
>     (_, _, Just b) -> (Close (b, Nothing), s)
>     _ | c == ' ' -> let (t, u) = span (== ' ') s in (Spc (1 + length t), u)
>     _ | c == '|' , (t, d : u) <- span boring s , Just b <- lookup d closers
>       -> (Close (b, Just t), u)
>     _ | c == '|' -> (Sym "|", s)
>     _ -> let (t, u) = span boring s in (Sym (c : t), u)

> slex :: String -> [STok]
> slex []       = []
> slex (c : s)  = let (t , s') = slex1 c s in t : slex s'

> data Elt
>   =  E STok
>   |  M Movement
>   |  B BType [Elt] (Either HowOpen BType)
>   deriving (Show, Eq)

> data Movement
>   = MOpen | MClose | MSOL | MEOL | MBang | MGnab deriving (Show, Eq)
> data HowOpen   = Banged | Dangling deriving (Show, Eq)

> type GStk    =  (Bwd GLayer, (Bwd Elt, CLine))
> type CLine   = (Behind, Bwd Elt, (), Ahead)
> type Behind  = Bwd (Bwd Elt, GSus)
> type Ahead   = Fwd (GSus, Bwd Elt)
> type GLayer  =  (Bwd Elt, (Behind, Bwd Elt, (BType, ()), Bwd Elt, Ahead))

> data GSus = BType :<> (Bwd Elt, (), Ahead)

> (<//) :: Bwd x -> [x] -> [x]
> (<//) = ala Endo foldMap (:)

> infixr 5 <//

> gEOF :: GStk -> [Elt]
> gEOF (yz, x) = yEOF yz (lEOF x) where
>   yEOF = ala Endo foldMap $ \ (lz, (ebz, ez, (b, ()), ez', bes)) ls ->
>     lz <// behind ebz (ez <// B b ls (Left Dangling) : ez' <// ahead bes)

> lEOF :: (Bwd Elt, CLine) -> [Elt]
> lEOF (lz, (ebz, ez, (), bes)) = lz <// behind ebz (ez <// ahead bes)

> behind :: Behind -> [Elt] -> [Elt]
> behind = ala Endo foldMap $ \ (ez, g) es -> ez <// cSus g : es

> ahead :: Ahead -> [Elt]
> ahead = foldMap $ \ (g, ez) -> cSus g : ez <// []

> cSus :: GSus -> Elt
> cSus (b :<> (ez, (), bes))
>   = B b (ez <// ahead bes) (Left Banged)

> gTok :: GStk -> STok -> GStk
> gTok (yz, (lz, (ebz, ez, (), bes))) (Open b)
>   = (yz :< (lz , (ebz, ez :< M MOpen, (b, ()), B0, bes)),
>      (B0, (B0, B0 :< M MSOL, (), F0)))
> gTok (yz :< (lz', (ebz', ez', (b', ()), ez'', bes')), x) (Close b)
>   | closes b' b
>   = (yz, (lz',
>     (ebz', ez' :< B b' (lEOF x) (Right b) <|> (ez'' :< M MClose), (), bes')))
> gTok (yz, (lz, (B0, ez, (), F0))) (Sym "\n")
>   = (yz, (lz <|> ez :< M MEOL, (B0, B0 :< M MSOL, (), F0)))
> gTok (yz, (lz, (ebz, ez, (), bes))) (Sym "\n")
>   = (yz, (lz, gNL (ebz, ez :< M MEOL, (), bes))) where
>       gNL (eb :< (ez, b), ez', (), bes) = gNL (eb, ez, (),  (b, ez') :> bes)
>       gNL (B0, ez, (), bes) = (B0, ez :< M MSOL, (), bes)
> gTok (yz, (lz, (ebz, ez, (), (b :<> (ez', (), bes'), ez'') :> bes)))
>   (Sym "!")
>   =  (yz :< (lz, (ebz, ez :< M MBang, (b, ()), ez'', bes)),
>        (ez', (B0, B0 :< M MSOL, (), bes')))
> gTok (yz :< (lz, (ebz, ez, (b, ()), ez'', bes)), (lz', (ebz', ez', (), F0)))
>   (Sym "!")
>   =  (yz, (lz,
>        (ebz :< (ez, b :<> gBang lz' (ebz', ez' :< M MGnab, (), F0)),
>          ez'', (), bes))) where
>     gBang lz' (ebz :< (ez', b), ez, (), bes)
>       = gBang lz' (ebz, ez', (), (b, ez) :> bes)
>     gBang lz' (B0, ez, (), bes) = (lz' <|> ez, (), bes)
> gTok (yz, (lz, (ebz, ez, (), bes))) t = (yz, (lz, (ebz, ez :< E t, (), bes)))

> doc :: [STok] -> [Elt]
> doc = go (B0, (B0, (B0, B0 :< M MSOL, (), F0))) where
>   go g [] = gEOF g
>   go g (t : ts) = mo (gTok g t) ts
>   mo (B0, (lz, x)) ts = lz <// go (B0, (B0, x)) ts
>   mo g ts = go g ts

> data BotTop x = Bot | Topped x | Top deriving (Show, Eq, Ord)

> lineAlone :: STok -> Bool
> lineAlone (Sym "data") = True
> lineAlone (Sym "let") = True
> lineAlone (Sym "lemma") = True
> lineAlone (Sym cs) | all ('-' ==) cs && length cs > 2 = True
> lineAlone _ = False

> lineStart :: STok -> Bool
> lineStart (Sym "<=") = True
> lineStart s = lineAlone s

> lefty :: BotTop Int -> [Elt] -> ([Elt], Bool, [Elt])
> lefty i (E s : ps)
>   | lineAlone s = ([E s], False, ps)
>   | lineStart s = (E s : qs, b, rs) where (qs, b, rs) = righty i ps
> lefty i ps = righty i ps

> righty :: BotTop Int -> [Elt] -> ([Elt], Bool, [Elt])
> righty i [] = ([], False, [])
> righty i ps@(E s : _) | lineStart s = ([], False, ps)
> righty i (p@(E (Sym ";")) : ps) = ([p], True, ps)
> righty i (M MSOL : E (Spc j) : ps)
>   | i < Topped j = (M MSOL : E (Spc j) : qs, b, rs)
>   where (qs, b, rs) = righty i ps
> righty i ps@(M MSOL : _) = ([], False, ps)
> righty i (p : ps) = (p : qs, b, rs) where (qs, b, rs) = righty i ps

> glomLine :: [Elt] -> Maybe ((BotTop Int, [Elt], Bool), [Elt])
> glomLine [] = Nothing
> glomLine (M MSOL : E (Spc i) : ps) =
>   Just ((Topped i, M MSOL : E (Spc i) : qs, b), rs)
>   where (qs, b, rs) = lefty (Topped i) ps
> glomLine (M MSOL : ps) =
>   Just ((Topped 0, M MSOL : qs, b), rs)
>   where (qs, b, rs) = lefty (Topped 0) ps
> glomLine ps = Just ((Top, qs, b), rs) where (qs, b, rs) = lefty Top ps

> dentLines :: [Elt] -> [(BotTop Int, [Elt], Bool)]
> dentLines = unfoldr glomLine

> data Nest = [Elt] :# [Nest] deriving Show

> nestDents :: BotTop Int -> [(BotTop Int, [Elt], Bool)] ->
>   ([Nest], [(BotTop Int, [Elt], Bool)])
> nestDents i [] = ([], [])
> nestDents i ((j, ps, b) : ls)
>   | i < j =
>     let (qs, rs) = if b then ([], ls) else nestDents j ls
>         (ss, ts) = nestDents i rs
>     in  ((ps :# qs) : ss, ts)
> nestDents i ls = ([], ls)

> nestLines :: [Elt] -> [Nest]
> nestLines = fst . nestDents Bot . dentLines

> ready :: String -> [Nest]
> ready = nestLines . doc . slex

> printNests :: Int -> [Nest] -> IO ()
> printNests i [] = return ()
> printNests i ((es :# qs) : rs) = do
>   putStr (take i (repeat ' '))
>   print es
>   printNests (i + 2) qs
>   printNests i rs
