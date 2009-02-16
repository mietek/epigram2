> module Lexer(
>   lexer, rexel,
>   LDoc,
>   LBloc,
>   Line (..),
>   LTok (..),
>   Brac (..), Bracket,
>   HC, width,
>   LeGt (..),
>   VC, vcs,
>   closer
>   ) where

> import Data.Monoid

INTERFACE

> type LDoc = [(VC, LLine)]

> lexer :: String -> LDoc
> lexer s = zip vcs (fmap (grok mempty) (lines s))

> rexel :: LDoc -> String
> rexel [] = ""
> rexel ((_, Blank) : ls) = '\n' : rexel ls
> rexel ((_, i :>->: ts) : ls) = spaces mempty i ++ lbloc mempty ts ++ "\n" ++
>   rexel ls

> newtype VC = VC Int deriving (Eq, Ord, Show)
> newtype HC = HC Int deriving (Eq, Ord, Show)

> data Dent b
>   = HC :>->: b
>   | Blank
>   deriving Show

> type LLine = Dent LBloc

> type LBloc = [(HC, LTok, HC)]

> data LTok
>   = LStuff String
>   | Opener Bracket
>   | Closer (Brac, Maybe ())
>   deriving Eq

> instance Show LTok where
>   show (LStuff s) = s
>   show (Opener (b, Just s)) = openc b : s ++ "|"
>   show (Opener (b, _)) = [openc b]
>   show (Closer (b, Just _)) = ['|', closec b]
>   show (Closer (b, _)) = [closec b]

> type Bracket = (Brac, Maybe String)
> data Brac = Rnd | Sqr | Crl deriving (Eq, Show)

> closer :: Bracket -> LTok
> closer (b, m) = Closer (b, m >> return ())

> instance Monoid HC where
>   mempty = HC 0
>   mappend (HC x) (HC y) = HC (x + y)

> width :: Char -> HC
> width c = HC 1

> data LeGt x
>   = LeBy x
>   | GtBy x

> class (Eq x, Ord x, Monoid x) => LEGT x where
>   legt :: x -> x -> LeGt x

> instance LEGT HC where
>   legt (HC i) (HC j) = if i <= j
>     then LeBy (HC (j - i))
>     else GtBy (HC (i - j))

> vcs :: [VC]
> vcs = fmap VC [0..]

IMPLEMENTATION

> openCB :: [(Char, Brac)]
> openCB = [('(', Rnd), ('[', Sqr), ('{', Crl)]

> openc :: Brac -> Char
> openc b = c where [c] = [c | (c, b') <- openCB, b == b']

> closeCB :: [(Char, Brac)]
> closeCB = [(')', Rnd), (']', Sqr), ('}', Crl)]

> closec :: Brac -> Char
> closec b = c where [c] = [c | (c, b') <- closeCB, b == b']

> spaces :: HC -> HC -> String
> spaces (HC i) (HC j) = take (j - i) (repeat ' ')

> lbloc :: HC -> LBloc -> String
> lbloc i [] = ""
> lbloc i ((j, t, k) : ts) = spaces i j ++ show t ++ lbloc k ts

> grok :: HC -> String -> LLine
> grok _ [] = Blank
> grok i (x : xs) | isSpace x = grok (i `mappend` width x) xs
> grok i xs = i :>->: chomp toks mempty xs

> data Chomp
>   = Eol Chomp
>   | Here (HC -> Chomp)
>   | Try (Char -> Maybe Chomp) Chomp
>   | Eat (Char -> Chomp)
>   | Out HC LTok Chomp
>   | LOut HC LTok HC Chomp

> chomp :: Chomp -> HC -> String -> LBloc
> chomp (Eol c) i [] = []
> chomp (Eol c) i xs = chomp c i xs
> chomp (Out j t c) i xs = (j, t, i) : chomp c i xs
> chomp (LOut j t l c) i xs = (j, t, l) : chomp c i xs
> chomp (Here f) i xs = chomp (f i) i xs
> chomp c i [] = chomp c i " "
> chomp (Try f e) i xs@(x : xs') = case f x of
>   Just c  -> chomp c (i `mappend` width x) xs'
>   _       -> chomp e i xs
> chomp (Eat f) i (x : xs) = chomp (f x) (i `mappend` width x) xs

> (??) :: (s -> Maybe t) -> (t -> u) -> s -> Maybe u
> (??) test yes s = fmap yes (test s)

> like :: (s -> Bool) -> s -> Maybe s
> like f x = if f x then Just x else Nothing

> toks :: Chomp
> toks =
>   Eol $
>   Try (like isSpace ?? \_ -> toks) $
>   Here $ \i ->
>     Try (flip lookup openCB ?? \b -> Here $ \j -> opToks i b j id) $
>     Try (flip lookup closeCB ?? \b -> Out i (Closer (b, Nothing)) toks) $
>     Try (like ('|' ==) ?? \_ -> barToks i) $
>     Try (like (`elem` solo) ?? \c -> Out i (LStuff [c]) toks) $
>     Eat $ \c -> tokToks i (c :)

> tokToks :: HC -> (String -> String) -> Chomp
> tokToks i s =
>   Try (like (not . isSpecial) ?? \c -> tokToks i (snoc s c)) $
>   Out i (LStuff (s "")) toks

> opToks :: HC -> Brac -> HC -> (String -> String) -> Chomp
> opToks i b j s =
>   Try (like ('|' ==) ?? \_ -> Out i (Opener (b, Just (s []))) toks) $
>   Try (like (not . isSpecial) ?? \c -> opToks i b j (snoc s c)) $
>   LOut i (Opener (b, Nothing)) j $ case s [] of
>     "" -> toks
>     n  -> Out j (LStuff n) toks

> barToks :: HC -> Chomp
> barToks i = Here $ \j ->
>   Try (flip lookup closeCB ?? \b -> Out i (Closer (b, Just ())) toks) $
>   Out i (LStuff "|") toks

> snoc :: (String -> String) -> Char -> String -> String
> snoc f c s = f (c : s)

> solo :: String
> solo = ",;"

> isSpace :: Char -> Bool
> isSpace = (' ' ==)

> isSpecial :: Char -> Bool
> isSpecial c = isSpace c || elem c specials where
>   specials = "|" ++ solo ++ fmap fst openCB ++ fmap fst closeCB
