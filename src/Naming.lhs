\section{Naming}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Naming (christen, christenREF, pINTM) where

> import Control.Applicative
> import Control.Monad
> import Data.Char
> import Data.Foldable hiding (elem)
> import Data.List
> import Data.Monoid

> import BwdFwd
> import Developments
> import Lexer
> import Parsley
> import Tm
> import TmParse

%endif


\subsection{Resolving Local Longnames}

For display and storage purposes, we have a system of local longnames
for referring to entries. We need to resolve those names as
references. We resolve \(f.x.y.z\) by searching outwards for $f$, then
inwards for a child $x$, $x$'s child $y$, $y$'s child $z$. References
are fully $\lambda$-lifted, but as $f$'s parameters are held in common
with the point of reference, we automatically supply them.

Any component of a local name may have a \textasciicircum|n| or |_n| suffix, where |n| is
an integer, representing a relative or absolute offset. A relative
offset \textasciicircum|n| refers to the $n^\mathrm{th}$ occurrence of the name
encountered when searching upwards, so |x|\textasciicircum|0| refers to the same reference
as |x|, but |x|\textasciicircum|1| skips past it and refers to the next thing named |x|.
An absolute offset |_n|, by contrast, refers to the exact numerical
component of the name. 

> data Offs = Rel Int | Abs Int deriving Show
> type RelName = [(String,Offs)]

> showRelName :: RelName -> String
> showRelName = intercalate "." . map f
>   where
>     f (x, Rel 0) = x
>     f (x, Rel i) = x ++ "^" ++ show i
>     f (x, Abs i) = x ++ "_" ++ show i


The |pINTM| function produces a parser for terms, given a context, by resolving
in the context all the names in the |InTm String| produced by |bigTmIn|.

> pINTM :: Bwd Entry -> P Tok INTM
> pINTM es = grok (resolver es B0 %) bigTmIn


The |resolver| function takes a context and a list of binder names, and
produces a mangler that, when applied, attempts to resolve the parameter
names in an |InTm String| to produce an |InTm REF|, i.e.\ an INTM.

> resolver :: Bwd Entry -> Bwd String -> Mangle Maybe String REF
> resolver ps vs = Mang
>     {  mangP  = \ x mes -> (|(|(findLocal ps vs) (parse pRelName x) @ |) $:$ mes|)
>     ,  mangV  = \ _ _ -> Nothing -- what's that index doing here?
>     ,  mangB  = \ x -> resolver ps (vs :< x)
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

> findGlobal :: Bwd Entry -> RelName -> Maybe EXTM
> findGlobal B0 sos = empty
> findGlobal (xs :< E r x e _) (y : ys) = case hits x y of
>     Right _  -> findChild r (foldMap boy xs) e ys
>     Left y'  -> findGlobal xs (y' : ys)
>   where
>     boy :: Entry -> Spine {TT} REF
>     boy (E r _ (Boy _) _)  = [A (N (P r))]
>     boy _                = []


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
>     findD (xs :< E r x e@(Girl _ _) _) (y : ys) as = case hits x y of
>         Right _  -> findChild r as e ys
>         Left y'  -> findD xs (y' : ys) as
>     findD _ sos as = empty


\subsection{Christening (Generating Local Longnames)}

Just as resolution automatically supplies parameters to references
which are actually lifted, so its inverse, \emph{christening}, must
hide parameters to lifted references which can be seen locally. For
example, here

\begin{alltt}
f [
  x : S
  g => t : T
  ] => g : T
\end{alltt}

$g$ is actually represented as $f.g f.x$, but should be displayed as, er, $g$.

Christening is thus the business of choosing a name for a reference in
scope by finding the shortest path to it from the referring term. The
common prefix of the name may thus be omitted, as may any common
parameters.


> christen :: Bwd Entry -> Name -> INTM -> InTm String
> christen es n tm = christener es n B0 %% tm

> christenREF :: Bwd Entry -> Name -> REF -> InTm String
> christenREF es n r = christen es n (N (P r))


> christener :: Bwd Entry -> Name -> Bwd String -> Mangle I REF String
> christener es n vs = Mang
>     {  mangP = \r as -> pure (mangleP es n vs r (unI as))
>     ,  mangV = \i _ -> pure (P (vs !. i))
>     ,  mangB = \v -> christener es n (vs :< v)
>     }
>   
> mangleP :: Bwd Entry -> Name -> Bwd String -> REF -> [Elim (InTm String)] -> ExTm String
> mangleP auncles me vs (target := _) args = 
>     let  (prefix, (t, n):targetSuffix) = splitNames me target
>          numBindersToSkip = getSum (foldMap (\x -> if x == t then Sum 1 else Sum 0) vs)
>          (ancestor, commonEntries, i) = findName auncles (prefix++[(t, n)]) t numBindersToSkip
>          args' = drop (bwdLength commonEntries) args
>     in  if targetSuffix == []
>         then  P (showRelName [(t, Rel i)]) $:$ args'
>         else  case ancestor of
>             E _ (x,_) (Boy _) _ ->
>                 error "mangleP: common ancestor is a boy, so it has no children"
>             E _ (x,_) (Girl LETG (kids, _, _)) _ -> 
>                 let  n = (t, Rel i) : (searchKids kids targetSuffix 0)
>                 in   P (showRelName n) $:$ args'





> searchKids :: Bwd Entry -> [(String, Int)] -> Int -> RelName
> searchKids _   []  _ = []
> searchKids B0  _   _ = error "searchKids: ran out of children"
> searchKids (es :< E _ (x, n) entity _) ((y, m):yms) i
>   | (x, n) == (y, m)  = case entity of
>       Boy _                     ->  if yms == []
>                                     then [(x, Rel i)]
>                                     else error "searchKids: it's mad uncle Quentin!"
>       (Girl LETG (kids, _, _))  ->  (x, Rel i):searchKids kids yms 0
>   | x == y            = searchKids es ((y, m):yms) (succ i)
>   | otherwise         = searchKids es ((y, m):yms) i


The |splitNames| function takes two names and returns their common prefix
along with the suffix of the second name.

> splitNames :: Name -> Name -> (Name, [(String, Int)])
> splitNames (x:xs) (y:ys)
>   | x == y        = let (p, s) = splitNames xs ys in (x:p, s)
> splitNames xs ys  = ([], ys)


The |findName| function searches a list of entries for a name, incrementing the
counter each time its string argument appears as the last component of an entry.
It returns the entry found, its prefix in the list of entries, and the count.

> findName :: Bwd Entry -> Name -> String -> Int -> (Entry, Bwd Entry, Int)
> findName (es :< e@(E (n := _) (x,_) _ _)) p y i
>   | n == p     = (e, es, i)                         
>   | x == y     = findName es p y (i+1)
>   | otherwise  = findName es p y i
> findName B0 _ _ _ = error "findName: ran out of ancestors"
