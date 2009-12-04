\section{Layout}

Here is a simplified layout parser for Epigram source, transforming
column-labelled tokens into lists of lines of tokens, nesting balanced brackets
and subordinate layout blocks.

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE RelaxedPolyRec, TypeSynonymInstances, RankNTypes #-}

%endif

> module Layout (layout, layTest) where

%if False

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Char
> import Data.List
> import Control.Arrow (first)

> import Lexer

%endif

> layout   :: [(Int, Tok)] -> [[Tok]]
> layTest  :: String -> [Tok]

\subsection{how to read layout}

Epigram 2 has layout, a bit like Haskell, but less fancy.

Firstly, consider each token sequence in balanced brackets to be nested inside
single bracket-token at the column of its opener. Bar the ruler line,

\begin{alltt}
0123456789
  f g (h
i j) k
\end{alltt}

has four nonspace tokens: \texttt{f} at column 2, \texttt{g} at 4,
\texttt{(..)} at 6, and \texttt{k} at 5.

A \(j\)-\emph{line} consists of an initial nonspace at column \(j\),
followed by tokens up to but not including a closing bracket, a
semicolon, or a nonspace at column \(\le j\).  The above is thus a
2-line.  An \(i\)-\emph{block} is a sequence of \(j\)-lines such that
\(i\le j\), separated by whitespace or semicolons at column \(\ge j\)

A \emph{layout token} in a bracket nests a \emph{layout keyword} with
a \(0\)-block. A layout token in a \(j\)-line nests a \emph{layout
keyword} with a \((j+1)\)-block. The current layout keywords are:

> lakeys :: [String]
> lakeys = ["where"]

Bar the ruler line, \begin{alltt}
012345678901234567890123456789
there's a place where I can go
    when I feel low
  when I feel blue
and it's my mind;
  and there's no time
\end{alltt}
is a \(0\)-block containing three lines: the first is a \(0\)-line finishing
with a layout token packing \texttt{where} with a \(1\)-block containing a
 \(22\)-line, a \(4\)-line, and a \(2\)-line; the second is the \(0\)-line
\texttt{and it's my mind}; the third is the \(2\)-line \texttt{and there's no
time}.

The |layout| function is charged with the task of recognizing a token sequence
as a \(0\)-block. This is reassuringly possible.


\subsection{a Monoid for blocks}

Documents, seen as nonempty sequences of lines, have a rather lovely
monoidal structure. The empty document is one empty line. Appending
two documents stitches the last line of one to the first line of the
other.

> newtype Lines = Lines {unl :: [[Tok]]} -- non-empty
> instance Monoid Lines where
>   mempty = Lines [[]]
>   mappend (Lines [xs]) (Lines (ys : yss)) = Lines ((xs ++ ys) : yss)
>   mappend (Lines (xs : xss)) y = Lines (xs : unl (mappend (Lines xss) y))

A line break looks like this:

> brk :: Lines
> brk = Lines [[], []]

A bunch of tokens can all be on one line like this:

> cur :: [Tok] -> Lines
> cur ts = Lines [ts]

Now, our lines will be token sequences consisting either entirely of
separators, or starting and ending with actual stuff. Where the physical
line-breaks show up is less important.


\subsection{a Monad for layout management}

We can use a straightforward consumer-producer combination.

> type L x = StateT [(Int, Tok)] (Writer x)
> instance Monoid x => Applicative (L x) where
>   pure = return
>   (<*>) = ap

Let's wrap up the stateful functionality we care about.
Firstly, we'll need to do local constructions, e.g. of
bracket contents.

> local :: Monoid x => L y a -> L x (a, y)
> local l = do
>   ((a, s'), y) <- (|runWriter (|runStateT ~ l get|)|)
>   put s'
>   return (a, y)

This control operator lets us look before we leap. The
process |l| can read \emph{but not write}\footnote{Cheeky
parametricity!}: it either gives
up (with a default), or commits and continues.

> look ::  Monoid x =>
>          (forall y. Monoid y => L y (Either a (L x a))) ->
>          L x a
> look l = do
>   s <- get
>   q <- l
>   case q of
>     Left a   -> put s >> return a
>     Right c  -> c

Now, the next couple of operators work well inside |look|,
growing the window of inputs under consideration without
necessarily committing to consuming them.
This thing reads spaces.

> space :: Monoid x => ([Tok] -> L x a) -> L x a
> space f = do
>   (iss, ius) <- (|span ~ (isSpcT . snd) get|)
>   put ius
>   f (map snd iss)

This thing reads the next token and its column. You
have to supply an action for end-of-file.

> next :: Monoid x => L x a -> (Int -> Tok -> L x a) -> L x a
> next n f = do
>   its <- get
>   case its of
>     []            -> n
>     (i, t) : its  -> put its >> f i t

Let's have a conditional |tell|, as it happens often.

> tellIf :: Monoid x => Bool -> x -> L x ()
> tellIf True   x  = tell x
> tellIf False  x  = (|()|)

If we stick to these gadgets, we're processing the file in
sequence, generating monoidal output. We have \emph{two} monoids
on the go: |[Tok]| and |Lines|.


\subsection{Managing Layout}

The hard work gets done by this function.

> lBody  ::  Int   -- block-left
>        ->  Int   -- line-left
>        ->  Bool  -- in middle of line?
>        ->  L Lines ()
> lBody i j b = look $ space $ \ ss -> next (|Left ~ ()|) $ \ k t -> case t of
>   _ | k < i  -> (|Left ~ ()|)          -- too far left, not ours
>   Clo _      -> (|Left ~ ()|)          -- closing bracket, not ours
>   Sem        -> return . Right $ do    -- semicolon, yes please
>     tellIf b brk                       -- ~ make a break if needed
>     tell $ cur (ss ++ [Sem])           -- ~ send separators
>     lBody i maxBound False             -- ~ any line start \(\ge i\) will do
>   t          -> return . Right $ do    -- commit
>     tellIf (b && k <= j) brk           -- ~ start of new line?
>     tell $ cur ss                      -- ~ send spaces
>     tellIf (k <= j) brk                -- ~ start of new line?
>     case t of                          -- ~ nested token?
>       Ope b                  -> tell =<< (|cur (braToks b)|)
>       Key w | elem w lakeys  -> tell =<< (|cur (layToks w (j + 1))|)
>       _                      -> tell $ cur [t]
>     lBody i (min j k) True             -- ~ new line left may decrease

We can use |lBody| to build a layout-token, for a given layout-keyword
and block-left. Parametricity tells you that nothing is writen!

> layToks :: Monoid x => String -> Int -> L x [Tok]
> layToks k i = do
>  ((), l) <- local $ lBody i maxBound False
>  (|[Lay k (unl l)]|)

Grabbing the body of a bracket is easier: keep going until you find a
close-bracket which matches. End-of-file or the wrong close-bracket
and we stop in a huff. Of course, we have to watch out for nested tokens
induced by nested open brackets, or layout.

> bBody :: Br -> L [Tok] (Maybe Br)
> bBody o = look $ next (|Left ~ Nothing|) $ \ _ t -> return $ case t of
>   Clo c  | brackets o c  -> Right (|Just ~ c|)
>          | otherwise     -> Left Nothing
>   Ope b                  -> Right $ do tell =<< braToks b;    bBody o
>   Key k | elem k lakeys  -> Right $ do tell =<< layToks k 0;  bBody o
>   t                      -> Right $ do tell [t] ; bBody o

We use |bBody| to build the token sequence resulting from a given
open-bracket. If we find a body with a matching close-bracket, we build
one nested token. If we're unhappy, we just dump the token stream out
as it was.

> braToks :: Monoid x => Br -> L x [Tok]
> braToks b = do
>   (mb, ts) <- local $ bBody b
>   case mb of
>     Just b' -> (|[Bra b ts b']|)
>     Nothing -> (|(Ope b : ts)|)

So we know how to process a file.

> layout its = unl . execWriter $ evalStateT (lBody 0 maxBound False) its
> layTest s = layout (tokenize s) !! 1
