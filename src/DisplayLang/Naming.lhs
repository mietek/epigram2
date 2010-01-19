\section{Naming}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, PatternGuards #-}

> module DisplayLang.Naming where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable hiding (elem, find)
> import Data.List
> import Data.Monoid
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import ProofState.Developments

> import DisplayLang.DisplayTm

> import Evidences.Tm
> import Evidences.Rules
> import Evidences.Mangler

%endif

\subsection{The Naming of Things}

For display and storage purposes, we have a system of local longnames for referring to entries.
Any component of a local name may have a \textasciicircum|n| or |_n| suffix, where |n| is
an integer, representing a relative or absolute offset. A relative
offset \textasciicircum|n| refers to the $n^\mathrm{th}$ occurrence of the name
encountered when searching upwards, so |x|\textasciicircum|0| refers to the same reference
as |x|, but |x|\textasciicircum|1| skips past it and refers to the next thing named |x|.
An absolute offset |_n|, by contrast, refers to the exact numerical
component of the name. 

> data Offs = Rel Int | Abs Int deriving Show
> type RelName = [(String,Offs)]

> type InTmRN = InTm RelName
> type ExTmRN = ExTm RelName
> type InDTmRN = InDTm RelName
> type ExDTmRN = ExDTm RelName

The |showRelName| function converts a relative name to a string by
inserting the appropriate punctuation.

> showRelName :: RelName -> String
> showRelName = intercalate "." . map f
>   where
>     f (x, Rel 0) = x
>     f (x, Rel i) = x ++ "^" ++ show i
>     f (x, Abs i) = x ++ "_" ++ show i

The |showName| function converts a name to a string absolutely (without christening).

> showName :: Name -> String
> showName = showRelName . map (\(x, i) -> (x, Abs i))


The |showEntries| function folds over a bunch of entries, christening them with the
given auncles and current name, and intercalating to produce a comma-separated list.

> showEntries :: (Traversable f, Traversable g) => Entries -> Name -> f (Entry g) -> String
> showEntries aus me = intercalate ", " . foldMap
>     (\(E ref _ _ _) -> [showRelName (christenREF aus me ref)])

The |showEntriesAbs| function works similarly, but uses absolute names instead of
christening them.

> showEntriesAbs :: Traversable f => f (Entry f) -> String
> showEntriesAbs = intercalate ", " . foldMap f
>   where
>     f e = [showName (entryName e)]


\subsection{Resolving Local Longnames}

We need to resolve local longnames as
references. We resolve \(f.x.y.z\) by searching outwards for $f$, then
inwards for a child $x$, $x$'s child $y$, $y$'s child $z$. References
are fully $\lambda$-lifted, but as $f$'s parameters are held in common
with the point of reference, we automatically supply them.


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


The |findGlobal| function takes a context and a relative name to resolve. It
searches the context for an entry that hits the name, then searches that
entry's children to resolve the next component. 

> findGlobal :: Entries -> RelName -> Either [String] (REF, Spine {TT} REF)
> findGlobal xs [(y, Rel 0)]
>   | Just ref <- lookup y primitives = Right (ref, [])
>   | Just ref <- lookup y axioms     = Right (ref, [])
> findGlobal B0 sos = Left ["findGlobal: couldn't find " ++ showRelName sos]
> findGlobal (xs :< e) (y : ys) = case hits (entryLastName e) y of
>     Right _  -> case e of
>         E r _ e _ -> findChild r (boySpine xs) e ys
>         M n (es, _, _) -> findInEntries es ys (boySpine xs)
>     Left y'  -> findGlobal xs (y' : ys)


The |findChild| function takes a reference to a containing entry, a spine of
shared parameters, an entity |e| and the remainder of a relative name to
resolve. If the remainder is empty, it returns a parameter referring to the
current entry (applied to the shared parameters if appropriate). Otherwise,
the entity should be a |Girl|, and it searches her children for the name.

> findChild :: REF -> Spine {TT} REF -> Entity Bwd -> RelName -> Either [String] (REF, Spine {TT} REF)
> findChild r  as (Boy _)              []  = Right (r,  [])
> findChild r  as (Girl _ _)           []  = Right (r,  as)
> findChild r  as (Boy _)              ys  = Left ["findChild: " ++ show r ++ " is a boy so it has no children!"]
> findChild r  as (Girl _ (es, _, _))  ys  = findInEntries es ys as


The |findInEntries| function takes a list of entries to search, a relative name
to look for and a spine of shared parameters. If it finds that the first
component of the name refers to a girl, it calls |findChild| to check if she or
one of her children is the target. Note that boys within other developments are
not in scope, but they may affect relative name offsets.

> findInEntries :: Entries -> RelName -> Spine {TT} REF -> Either [String] (REF, Spine {TT} REF)
> findInEntries (xs :< M n (es, _, _)) (y : ys) as = case hits (last n) y of
>     Right _  -> findInEntries es ys as
>     Left y'  -> findInEntries xs (y' : ys) as
> findInEntries (xs :< E r x e@(Girl _ _) _) (y : ys) as = case hits x y of
>     Right _  -> findChild r as e ys
>     Left y'  -> findInEntries xs (y' : ys) as
> findInEntries (xs :< E _ x (Boy _) _) (y : ys) as = case hits x y of
>     Right _  -> Left ["findInEntries: " ++ show x ++ " is a boy, so it has no children!"]
>     Left y'  -> findInEntries xs (y' : ys) as
> findInEntries B0  sos  as = Left ["findInEntries: ran out of entries looking for "
>                                     ++ showRelName sos]
> findInEntries _   []   as = Left ["findInEntries: modules have no term representation."]


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


The |christenName| and |christenREF| functions do a similar job for names, and
the name part of references, respectively.

> christenName :: Entries -> Name -> Name -> RelName
> christenName es me target = case mangleP es me B0 target [] of DP x -> x
>
> christenREF :: Entries -> Name -> REF -> RelName
> christenREF es me (target := _) = christenName es me target


The |mangleP| function takes a list of entries in scope, the name of the curent
location, a list of local variables, the name of the parameter to christen and a
spine of arguments. It gives an appropriate relative name to the parameter and
applies it to the arguments --- \emph{for girls}, dropping any that are shared with the current location.

> mangleP :: Entries -> Name -> Bwd String -> Name -> DSpine RelName -> ExDTmRN
> mangleP aus me vs target args = DP s $::$ drop n args
>   where (s, n) = baptise aus me vs target


The |baptise| function takes a list of entries in scope, the name of the curent
location, a list of local variables and the name of the parameter to christen.
It returns an appropriate relative name and the number of arguments to drop. 

> baptise :: Entries -> Name -> Bwd String -> Name -> (RelName, Int)
> baptise auncles me vs target = case splitNames me target of
>   (prefix, (t, n):targetSuffix) ->
>     let  numBindersToSkip = ala Sum foldMap (indicator (t ==)) vs
>          boyCount = ala Sum foldMap (indicator (not. entryHasDev))
>     in
>       case findName auncles (prefix++[(t, n)]) t numBindersToSkip of
>         Just (ancestor, commonEntries, i) -> 
>             let argsToDrop | entryHasDev ancestor  = boyCount commonEntries
>                            | otherwise             = 0
>             in  if targetSuffix == []
>                 then  ([(t, Rel i)], argsToDrop)
>                 else
>                   let  (kids, _, _) = entryDev ancestor
>                        n = (t, Rel i) : (searchKids kids targetSuffix 0)
>                   in   (n, argsToDrop)
>         Nothing -> tryBuiltins
>   (prefix, []) -> tryBuiltins
>  where
>    tryBuiltins :: (RelName, Int)
>    tryBuiltins = case find ((target ==) . refName . snd) (axioms ++ primitives) of
>       Just (s, _)  -> ([(s, Rel 0)], 0)
>       Nothing      -> ([("???" ++ showName target, Rel 0)], 0)


The |searchKids| function searches a list of children to match a name suffix, producing
a relative name corresponding to the suffix. It should be called with the counter set
to zero, which then is incremented to determine the relative offset of each name component.

> searchKids :: Entries -> [(String, Int)] -> Int -> RelName
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

> findName :: Entries -> Name -> String -> Int -> Maybe (Entry Bwd, Entries, Int)
> findName (es :< e) p y i
>   | entryName e == p     = Just (e, es, i)                         
>   | fst (entryLastName e) == y     = findName es p y (i+1)
>   | otherwise  = findName es p y i
> findName B0 p _ _ = Nothing



Just in case it is useful, here is a simple christener that assigns absolute names.

> christenAbs :: INTM -> InTm String
> christenAbs tm = christenerAbs B0 %% tm

> christenerAbs :: Bwd String -> Mangle Identity REF String
> christenerAbs vs = Mang
>     {  mangP = \(name := _) as -> pure (P (showName name))
>     ,  mangV = \i _ -> pure (P (vs !. i))
>     ,  mangB = \v -> christenerAbs (vs :< v)
>     }
